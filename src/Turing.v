Require Import Coq.Setoids.Setoid.
Require Import Coq.Bool.Bool.
Require Import Coq.Logic.Classical_Prop.

  (** These are the assumptions of our theory: *)
  (** We leave the input and the machine as unspecified data types. *)
  Parameter input: Type.
  Axiom input_inhabited: input.
  (** Equality over the input is decidable. *)
  Parameter input_eq_dec: forall x y: input, {x = y} + {x <> y}.
  Parameter machine: Type.

  (** Let us say we have a function that can encode and decode a pair of
      inputs. *)
  Parameter decode_pair : input -> (input * input).
  Parameter encode_pair: (input * input) -> input.
  Axiom decode_encode_pair_rw:
    forall p,
    decode_pair (encode_pair p) = p.
  Axiom encode_decode_pair_rw:
    forall w,
    encode_pair (decode_pair w) = w.
  Axiom encode_pair_ext:
    forall w1 w2,
    encode_pair w1 = encode_pair w2 ->
    w1 = w2.
  Axiom decode_pair_ext:
    forall p1 p2,
    decode_pair p1 = decode_pair p2 ->
    p1 = p2.

  (** A language is a function that given an input (a word) holds if, and only if,
      that word is in the language. Thus, [L w] is the same as saying $w \in L$.
    *)

  Definition lang := input -> Prop.

  (** The result of running a Turing machine. *)
  Inductive result :=
    | Halt: bool -> result
    | Loop: result.

  (** We can run a machine and obtain its run result. *)
  Parameter Exec: machine -> input -> result -> Prop.
  Parameter exec_fun: forall m i r1 r2,
    Exec m i r1 ->
    Exec m i r2 ->
    r1 = r2.
  Parameter exec_exists:
    forall m i,
    exists r, Exec m i r.
  (** When running two programs in parallel, we get to know
      which of the two programs has terminated and how they
      terminated. *)
  Inductive par_result :=
  | pleft: bool -> par_result
  | pright: bool -> par_result
  | pboth: bool -> bool -> par_result.

  Inductive Prog :=
  | Read: (input -> Prog) -> Prog
  | Call: Prog -> input -> Prog
    (**
     `Seq p1 f`: run p1, if p1 terminates, then
     run (f r) where `r` is a boolean that states if p1
     accepted or rejected its input.
    *)
  | Seq: Prog -> (bool -> Prog) -> Prog
    (**
      Calls a machine with a given input
      (see Universal Turing Machines)
     *)
  | Tur: machine -> Prog
    (**
      This Turing Machine just accepts/loops/rejects without
      any further operation.
      *)
  | Ret: result -> Prog
    (**
      `Par p1 p2 f` interleaves the exection of program `p1`
      and `p2`. If either (or both) terminate, then
      call `f` with the termination result. 
     *) 
  | Par: Prog -> Prog -> (par_result -> Prog) -> Prog.

  Parameter par_choice: Prog -> Prog -> bool -> bool -> par_result. 
  Inductive ParChoice b1 b2: par_result -> Prop :=
  | par_choice_left:
    ParChoice b1 b2 (pleft b1)
  | par_choice_right:
    ParChoice b1 b2 (pright b2)
  | par_choice_both:
    ParChoice b1 b2 (pboth b1 b2).

  (** The parallel choice must respect the result *)
  Axiom par_choice_spec:
    forall p q b1 b2 r,
    par_choice p q b1 b2 = r ->
    ParChoice b1 b2 r.

  (**
    These describe the axiomatic semantics of turing machines.
    We can run a program `p` and obtain a resul `r` with
    `Run p r`.
    *)
  Inductive Run: Prog -> input -> result -> Prop :=
  | run_read:
    forall p i r,
    Run (p i) i r ->
    Run (Read p) i r
  | run_call:
    forall p i j r,
    Run p i r ->
    Run (Call p i) j r 
  | run_ret:
    (** We can directly return a result *)
    forall r i,
    Run (Ret r) i r
  | run_tur:
    (** Calling a machine is the same as using function `run`. *)
    forall m i r,
    Exec m i r ->
    Run (Tur m) i r
  | run_seq_cont:
    (** If `p` terminates and returns `b`, then we can
       proceed with the execution of `q b`. *) 
    forall p q b r i,
    Run p i (Halt b) ->
    Run (q b) i r ->
    Run (Seq p q) i r
  | run_seq_loop:
    (** If `p` loops, then `p; q` also loops. *)
    forall p q i,
    Run p i Loop ->
    Run (Seq p q) i Loop
  | run_par_l_seq:
    (** If `p` terminates and `q` loops, then
       we run continuation `c` with `cleft b`. *)
    forall p q c r b i,
    Run p i (Halt b) ->
    Run q i Loop ->
    Run (c (pleft b)) i r ->
    Run (Par p q c) i r
  | run_par_r_seq:
    (** If `p` loops and `q` terminates, then
       we run continuation `c` with `cright b`. *)
    forall p q c r b i,
    Run p i Loop ->
    Run q i (Halt b) ->
    Run (c (pright b)) i r ->
    Run (Par p q c) i r
  | run_par_both:
    (** If both `p` and `q` terminate, then
       we run continuation `c` with `pboth b1 b2`. *)
    forall p1 p2 c r b1 b2 i,
    Run p1 i (Halt b1) ->
    Run p2 i (Halt b2) ->
    Run (c (par_choice p1 p2 b1 b2)) i r ->
    Run (Par p1 p2 c) i r
  | run_par_loop:
    (** If both `p` and `q` loop, then the whole thing loops. *)
    forall p q c i,
    Run p i Loop ->
    Run q i Loop ->
    Run (Par p q c) i Loop.

  (** We define a notation for sequencing. *)
  Notation "'mlet' x <- e 'in' c" := (Seq e (fun x => c)) (at level 60, right associativity).
  (** We define a notion for parallel sequencing. *)
  Notation "'plet' x <- e1 '\\' e2 'in' c" := (Par e1 e2 (fun (x:par_result) => c)) (at level 60, right associativity).
  (** Notation for ACCEPT means returning Accept *)
  Notation ACCEPT := (Ret (Halt true)).
  (** Notation for LOOP means returning Reject *)
  Notation REJECT := (Ret (Halt false)).
  (** Notation for LOOP means returning Loop *)
  Notation LOOP := (Ret Loop).

  (** We also define a function to serialize a machine into a string (of type
      input). In the book, this corresponds to notation <M>. *)
  Parameter encode_prog: Prog -> input.
  (** Similarly, we have a function that takes a string and produces a machine.
      In the book, this corresponds to notation M = <M> *)
  Parameter decode_prog: input -> Prog.
  (** Decoding and encoding a machine yields the same machine. *)
  Axiom decode_encode_prog_rw:
    forall m,
    decode_prog (encode_prog m) = m.
  Axiom encode_decode_prog_rw:
    forall w, encode_prog (decode_prog w) = w.
  Axiom encode_prog_ext:
    forall m1 m2,
    encode_prog m1 = encode_prog m2 -> m1 = m2.

  Axiom decode_prog_ext:
    forall w1 w2,
    decode_prog w1 = decode_prog w2 -> w1 = w2.

  (** Given a machine and a string, encodes the pair as a string.
      In the book, this corresponds to notation <M, w>. *)
  Definition encode_prog_input (M:Prog) (w:input) : input :=
    encode_pair (encode_prog M, w).

  (** Given a string this function deserializes a pair M and w, given an encoded
      string <M,w>. *)
  Definition decode_prog_input p := let (M, w) :=
    decode_pair p in (decode_prog M, w).

  (** Decoding and encoding a pair yields the same pair. *)
  Lemma decode_encode_prog_input_rw:
    forall M w,
    decode_prog_input
          (encode_prog_input M w) = (M, w).
  Proof.
    intros.
    unfold decode_prog_input.
    unfold encode_prog_input.
    rewrite decode_encode_pair_rw.
    rewrite decode_encode_prog_rw.
    reflexivity.
  Qed.

  Lemma decode_prog_input_ext:
    forall i1 i2,
    decode_prog_input i1 = decode_prog_input i2 ->
    i1 = i2.
  Proof.
    unfold decode_prog_input.
    intros.
    destruct (decode_pair i1) as (M1, j1) eqn:R1.
    destruct (decode_pair i2) as (M2, j2) eqn:R2.
    inversion H; subst; clear H.
    apply decode_prog_ext in H1.
    subst.
    rewrite <- R1 in R2.
    apply decode_pair_ext in R2.
    auto.
  Qed.

  Lemma decode_prog_input_rev:
    forall w M i,
    decode_prog_input w = (M, i) ->
    w = encode_prog_input M i.
  Proof.
    intros.
    rewrite <- decode_encode_prog_input_rw in H.
    apply decode_prog_input_ext in H.
    assumption.
  Qed.

  Lemma encode_prog_input_ext:
    forall M M' i i',
    encode_prog_input M i = encode_prog_input M' i' -> M = M' /\ i = i'.
  Proof.
    unfold encode_prog_input.
    intros.
    apply encode_pair_ext in H.
    inversion H; subst; clear H.
    apply encode_prog_ext in H1.
    auto.
  Qed.

  (** Let us define an abbreviation of the above functions. *)
  Notation "'<<' w1 ',' w2 '>>'" := (encode_pair w1 w2).
  Notation "'[[' M ']]'" := (encode_prog M).
  Notation "'<[' M , w ']>'" := (encode_prog_input M w).


  (** Define the equivalence of languages *)
  Definition Equiv (L1 L2:lang) :=
    forall i,
    L1 i <-> L2 i.

  Definition Impl (L1 L2:lang) := 
    forall w,
    L1 w -> L2 w.

  Notation "A ≡ B" := (Equiv A B) (at level 80, right associativity).

  (** We use a direct definition of recognition:
      The turing machine accepts input i (with `run m i`)
      iff language L accepts i.
       *)

  Definition Recognizes (p:Prog) (L:lang) :=
    forall i, Run p i (Halt true) <-> L i.

  Lemma recognizes_def:
    forall p (L:lang),
    (forall i, Run p i (Halt true) -> L i) ->
    (forall i, L i -> Run p i (Halt true)) ->
    Recognizes p L.
  Proof.
    intros.
    unfold Recognizes.
    intros; split; auto.
  Qed.

  Lemma recognizes_impl:
    forall m L1 L2,
    Equiv L1 L2 ->
    Recognizes m L1 ->
    Recognizes m L2.
  Proof.
    intros.
    unfold Recognizes in *.
    intros.
    rewrite H0.
    apply H.
  Qed.

  Lemma equiv_symm:
    forall L1 L2,
    Equiv L1 L2 <-> Equiv L2 L1.
  Proof.
    unfold Equiv; split; intros.
    - rewrite H.
      intuition.
    - rewrite H.
      intuition.
  Qed.

  Lemma equiv_trans:
    forall L1 L2 L3,
    Equiv L1 L2 ->
    Equiv L2 L3 ->
    Equiv L1 L3.
  Proof.
    unfold Equiv; intros.
    rewrite H.
    rewrite H0.
    intuition.
  Qed.

  Lemma equiv_refl:
    forall L,
    Equiv L L.
  Proof.
    split; intros; tauto.
  Qed.

  Lemma equiv_sym:
    forall L1 L2,
    Equiv L1 L2 ->
    Equiv L2 L1.
  Proof.
    unfold Equiv; split; intros; apply H; assumption.
  Qed.

  (** Register [Equiv] in Coq's tactics. *)
  Global Add Parametric Relation : lang Equiv
    reflexivity proved by equiv_refl
    symmetry proved by equiv_sym
    transitivity proved by equiv_trans
    as l_equiv_setoid.

  Import Morphisms.

  Global Instance recognizes_equiv_proper: Proper (eq ==> Equiv ==> iff) Recognizes.
  Proof.
    unfold Proper, respectful, Equiv, Recognizes.
    intros.
    split; intros; split; intros; subst;
    try (apply H0; apply H1; auto);
    try (apply H1; apply H0; auto).
  Qed.


  (** A language is recognizable, that is
      there is some machine m that recognizes it. *)

  Definition Recognizable (L:lang) : Prop :=
    exists m, Recognizes m L.

  Global Instance recognizable_equiv_proper: Proper (Equiv ==> iff) Recognizable.
  Proof.
    unfold Proper, respectful, Recognizable.
    intros.
    split; intros (m, Hx).
    - rewrite H in Hx.
      eauto.
    - rewrite <- H in Hx.
      eauto.
  Qed.

  Lemma recognizable_def:
    forall m L, Recognizes m L -> Recognizable L.
  Proof.
    intros.
    exists m.
    assumption.
  Qed.


  Lemma run_read_rw:
    forall f i r,
    Run (Read f) i r <-> Run (f i) i r.
  Proof.
    split; intros.
    - inversion H; subst; auto.
    - constructor; assumption.
  Qed.

  Lemma run_call_rw:
    forall p i j r,
    Run (Call p j) i r <-> Run p j r.
  Proof.
    split; intros.
    - inversion H; subst; auto.
    - constructor; auto.
  Qed.

  (*----------------------------------------------------------------------------*)

  Section RecognizesRun.

    Ltac clear_result :=
      match goal with
        | [ H: Halt _ = Loop |- _ ] =>
          inversion H
        | [ H: Loop = Halt _ |- _ ] => inversion H
        | [ H: Loop = Loop |- _ ] => clear H
        | [ H1: Halt ?b1 = Halt ?b2 |- _] =>
          inversion H1; subst; clear H1
        end.

    Lemma run_fun:
      forall p i r1,
      Run p i r1 ->
      forall r2,
      Run p i r2 ->
      r1 = r2.
    Proof.
      intros p i r1 H; induction H; intros r' He;
        inversion He; subst; clear He; auto;
        (* In each case we have a bunch of Run's that are solved
           by induction; we need to make sure we clear any dec's,
           so that we can advance to the next IH *) 
        repeat match goal with
        | [ H1: Run ?q i ?r1, H2: Run ?q i ?r2 |- _] =>
          (
            assert (r1 = r2) by eauto ||
            assert (r2 = r1) by eauto
          ); subst; clear H2; try clear_result; auto
        end;
        try clear_result;
        auto.
      eauto using exec_fun.
    Qed.

    Lemma run_exists:
      forall p i,
      exists r, Run p i r.
    Proof.
      induction p; intros.
      - assert (H := H i i).
        destruct H as (r, Hr).
        exists r.
        constructor; auto.
      - assert (IHp := IHp i).
        destruct IHp as (r, IHp).
        exists r.
        constructor.
        assumption.
      - assert (IHp := IHp i).
        destruct IHp as ([], IHp).
        + assert (H := H b i).
          destruct H as (r, H).
          exists r.
          eapply run_seq_cont; eauto.
        + exists Loop.
          constructor.
          assumption.
      - destruct (exec_exists m i) as (r, He).
        exists r.
        constructor.
        assumption.
      - exists r.
        constructor.
      - assert (IHp1 := IHp1 i).
        assert (IHp2 := IHp2 i).
        destruct IHp1 as (r1, Hr1).
        destruct IHp2 as (r2, Hr2).
        destruct r1, r2.
        + assert (H := H (par_choice p1 p2 b b0) i).
          destruct H as (r, Hr).
          exists r.
          eapply run_par_both; eauto.
        + assert (H := H (pleft b) i).
          destruct H as (r, Hr).
          exists r.
          eapply run_par_l_seq; eauto.
        + assert (H := H (pright b) i).
          destruct H as (r, Hr).
          exists r.
          eapply run_par_r_seq; eauto.
        + exists Loop.
          constructor; auto.
    Qed.

    Lemma recognizes_run_reject:
      forall p L i,
      Recognizes p L ->
      Run p i (Halt false) ->
      ~ L i.
    Proof.
      intros.
      intros N.
      apply H in N.
      assert (Hx: Halt true = Halt false) by eauto using run_fun.
      inversion Hx.
    Qed.

    Lemma recognizes_run_accept:
      forall p L,
      Recognizes p L ->
      forall i,
      Run p i (Halt true) ->
      L i.
    Proof.
      intros.
      apply H.
      assumption.
    Qed.


    Lemma recognizes_not_accept:
      forall p L i,
      Recognizes p L ->
      ~ L i ->
      ~ Run p i (Halt true).
    Proof.
      intros.
      intros N.
      assert (L i). { eapply recognizes_run_accept; eauto. }
      contradiction.
    Qed.

    Lemma recognizes_accept:
      forall p L i,
      Recognizes p L ->
      L i ->
      Run p i (Halt true).
    Proof.
      intros.
      apply H in H0.
      assumption.
    Qed.

    Lemma recognizes_run_loop:
      forall p L,
      Recognizes p L ->
      forall i,
      Run p i Loop ->
      ~ L i.
    Proof.
      intros.
      intros N.
      apply H in N.
      assert (Hx: Loop = Halt true) by eauto using run_fun.
      inversion Hx.
    Qed.

    Lemma recognizes_accept_rw:
      forall p L,
      Recognizes p L ->
      forall i,
      Run p i (Halt true) <-> L i.
    Proof.
      split; intros.
      - eapply recognizes_run_accept; eauto.
      - eapply recognizes_accept; eauto.
    Qed.

    Lemma lang_equiv:
      forall L1 L2,
      Equiv L1 L2 ->
      forall m,
      Recognizes m L1 <-> Recognizes m L2.
    Proof.
      split; unfold Recognizes; intros.
      - rewrite H0.
        auto.
      - rewrite H0.
        symmetry.
        auto.
    Qed.
  End RecognizesRun.

  (*----------------------------------------------------------------------------*)

  Section Complement.
    Definition compl L : lang := fun i => not (L i).

    Lemma co_co_rw:
      forall L,
      Equiv (compl (compl L)) L.
    Proof.
      intros.
      unfold Equiv.
      split; intros. {
        destruct (Classical_Prop.classic (L i)). {
          assumption.
        }
        apply H in H0.
        inversion H0.
      }
      unfold compl.
      intros N.
      contradiction.
    Qed.

    Lemma co_recognizes_run_accept:
      forall m L i,
      Recognizes m (compl L) ->
      Run m i (Halt true) ->
      ~ L i.
    Proof.
      intros.
      apply recognizes_run_accept with (L:=compl L) in H0; auto.
    Qed.

    Lemma co_recognizes_not_accept:
      forall m L i,
      Recognizes m (compl L) ->
      L i ->
      ~ Run m i (Halt true).
    Proof.
      intros.
      intros N.
      apply H in N.
      contradiction.
    Qed.

    Lemma co_recognizes_accept:
      forall m L i,
      Recognizes m (compl L) ->
      ~ L i ->
      Run m i (Halt true).
    Proof.
      intros.
      unfold compl in *.
      apply H in H0.
      assumption.
    Qed.

  End Complement.

  (*----------------------------------------------------------------------------*)

  Section Decidable.
    (** We define a decider as any Turing Machine that returns either Accept or
        Reject, but not Loop. *)
    Definition Decider (p:Prog) := forall i, exists b, Run p i (Halt b).

    Lemma decider_def:
      forall p,
      (forall i, exists b, Run p i (Halt b)) ->
      Decider p.
    Proof.
      intros.
      unfold Decider; intros. eauto.
    Qed.

    Definition Decides m L := Recognizes m L /\ Decider m.

    Lemma decides_def:
      forall m L,
      Recognizes m L ->
      Decider m ->
      Decides m L.
    Proof.
      intros.
      split; assumption.
    Qed.

    Definition Decidable L := exists m, Decides m L.

    Lemma decidable_def:
      forall m L, Decides m L -> Decidable L.
    Proof.
      intros.
      exists m.
      assumption.
    Qed.

    Lemma decidable_to_recognizable:
      forall L,
      Decidable L ->
      Recognizable L.
    Proof.
      intros.
      destruct H as (m, H).
      destruct H.
      apply recognizable_def with (m:=m).
      assumption.
    Qed.

    Lemma unrecognizable_to_undecidable:
      forall L,
       ~ Recognizable L ->
       ~ Decidable L.
    Proof.
      intros.
      intros N.
      apply decidable_to_recognizable in N.
      contradiction.
    Qed.

    Lemma decides_to_recognizes:
      forall m L,
      Decides m L ->
      Recognizes m L.
    Proof.
      intros.
      destruct H.
      assumption.
    Qed.

    Lemma decides_run_reject:
      forall m L i,
      Decides m L ->
      Run m i (Halt false) ->
      ~ L i.
    Proof.
      intros.
      apply decides_to_recognizes in H.
      apply recognizes_run_reject with (p:=m); auto.
    Qed.

    Lemma decides_run_accept:
      forall m L i,
      Decides m L ->
      Run m i (Halt true) ->
      L i.
    Proof.
      intros.
      apply decides_to_recognizes in H.
      apply recognizes_run_accept with (p:=m); auto.
    Qed.

    Lemma decides_accept:
      forall m L i,
      Decides m L ->
      L i ->
      Run m i (Halt true).
    Proof.
      intros.
      apply decides_to_recognizes in H.
      apply recognizes_accept with (L:=L); auto.
    Qed.

    Lemma decides_inv_run_result:
      forall p L,
      Decides p L ->
      forall i r,
      Run p i r ->
      exists b, r = Halt b.
    Proof.
      intros.
      destruct H as (Ha, Hb).
      destruct (Hb i);
      eauto using run_fun.
    Qed.

    Lemma decider_to_run:
      forall p,
      Decider p ->
      forall i,
      exists b, Run p i (Halt b).
    Proof.
      intros.
      unfold Decider in *.
      auto.
    Qed.

    Lemma decides_to_run:
      forall p L,
      Decides p L ->
      forall i,
      exists b, Run p i (Halt b).
    Proof.
      intros.
      destruct H.
      eauto.
    Qed.

    Lemma decider_not_reject:
      forall p i,
      Decider p ->
      ~ Run p i (Halt false) ->
      Run p i (Halt true).
    Proof.
      intros.
      edestruct decider_to_run with (i:=i) as (b, Hr); eauto.
      destruct b;
      intuition.
    Qed.

    Lemma decider_not_accept:
      forall m i,
      Decider m ->
      ~ Run m i (Halt true) ->
      Run m i (Halt false).
    Proof.
      intros.
      edestruct decider_to_run with (i:=i) as (b, Hr); eauto.
      destruct b; intuition.
    Qed.

    Lemma decides_to_decider:
      forall m L,
      Decides m L ->
      Decider m.
    Proof.
      intros.
      unfold Decides in *.
      destruct H; assumption.
    Qed.

    Lemma decides_reject:
      forall m L i,
      Decides m L ->
      ~ L i ->
      Run m i (Halt false).
    Proof.
      intros.
      destruct H.
      apply decider_to_run with (i:=i) in H1.
      destruct H1 as ([], Hr).
      - apply recognizes_run_accept with (L:=L) in Hr; auto.
        contradiction.
      - assumption.
    Qed.

    Lemma decider_no_loop:
      forall m i,
      Decider m ->
      ~ Run m i Loop.
    Proof.
      intros.
      unfold Decider in *.
      intros N.
      destruct (H i) as ([], Ha).
      - assert (M: Loop = Halt true) by eauto using run_fun; inversion M.
      - assert (M: Loop = Halt false) by eauto using run_fun; inversion M.
    Qed.

    Lemma decides_no_loop:
      forall m L,
      Decides m L ->
      forall i,
      ~ Run m i Loop.
    Proof.
      intros.
      destruct H.
      eapply decider_no_loop; eauto.
    Qed.


  End Decidable.

  (**
    A Theory to reason about recognizability/decidability directly on
    programs.
    *)
  Section HALTS.

    (* A program halts *)
    Inductive Halts: Prog -> input -> Prop :=
    | halts_read:
      forall p i,
      Halts (p i) i ->
      Halts (Read p) i
    | halts_call:
      forall p i j,
      Halts p j ->
      Halts (Call p j) i
    | halts_ret:
      forall i b,
      Halts (Ret (Halt b)) i
    | halts_tur:
      forall m i b,
      Exec m i (Halt b) ->
      Halts (Tur m) i
    | halts_seq:
      forall p i b q,
      Run p i (Halt b) ->
      Halts (q b) i ->
      Halts (mlet x <- p in q x) i
    | halts_par_l_seq:
      forall p q i b c,
      Run p i (Halt b) ->
      Run q i Loop ->
      Halts (c (pleft b)) i ->
      Halts (Par p q c) i
    | halts_par_r_seq:
      forall p q i b c,
      Run p i Loop ->
      Run q i (Halt b) ->
      Halts (c (pright b)) i ->
      Halts (Par p q c) i
    | halts_par_both:
      forall p q i b1 b2 c,
      Run p i (Halt b1) ->
      Run q i (Halt b2) ->
      Halts (c (par_choice p q b1 b2)) i ->
      Halts (Par p q c) i.

    Lemma run_to_halts:
      forall p i b,
      Run p i (Halt b) ->
      Halts p i.
    Proof.
      intros p i b Hr.
      remember (Halt b).
      generalize dependent b.
      induction Hr; intros b' Hb; subst.
      try (apply IHHr in Hdec; clear IHHr).
      - constructor; eauto.
      - constructor; eauto.
      - constructor.
      - econstructor; eauto.
      - econstructor; eauto.
      - inversion Hb.
      - eapply halts_par_l_seq; eauto.
      - eapply halts_par_r_seq; eauto.
      - eapply halts_par_both; eauto.
      - inversion Hb.
    Qed.

    Lemma halts_to_run:
      forall p i,
      Halts p i ->
      exists b, Run p i (Halt b).
    Proof.
      intros.
      induction H;
        try (destruct IHHalts as (b', IH));
        try (exists b'; constructor; assumption; fail);
        try (exists b; constructor; assumption; fail);
        exists b'.
      - eapply run_seq_cont; eauto.
      - eapply run_par_l_seq; eauto.
      - eapply run_par_r_seq; eauto.
      - eapply run_par_both; eauto.
    Qed.

    Lemma halts_rw:
      forall p i,
      (exists b, Run p i (Halt b)) <-> Halts p i.
    Proof.
      split; intros.
      - destruct H. eauto using run_to_halts.
      - auto using halts_to_run.
    Qed.

    Lemma decider_to_halts:
      forall p,
      Decider p ->
      forall i,
      Halts p i.
    Proof.
      intros.
      rewrite <- halts_rw.
      auto.
    Qed.

    Lemma halts_to_decider:
      forall p,
      (forall i, Halts p i) ->
      Decider p.
    Proof.
      intros.
      unfold Decider.
      intros.
      rewrite halts_rw.
      auto.
    Qed.

    Lemma decides_to_halts:
      forall p L,
      Decides p L ->
      forall i,
      Halts p i.
    Proof.
      intros.
      destruct H.
      auto using decider_to_halts.
    Qed.
 
  End HALTS.

  (** Tactics that simplify `Run` objects in the assumptions. *)

  Ltac run_simpl_inv :=
  match goal with
  | [ H: _ |- _ ] =>
    match type of H with
      | Run (Call _ _) _ _ => idtac
      | Run (Read _) _ _ => idtac
      | Run (Tur _) _ _ => idtac
      | Run (Ret _) _ _ => idtac
      | _ => fail
    end;
    inversion H; subst; clear H
  end.

  Ltac run_simpl_explode :=
    match goal with
    | [ H: _ |- _ ]  =>
        match type of H with
        | true = true => idtac
        | false = false => idtac

        | false = true => idtac
        | true = false => idtac

        | Halt true = Halt true => idtac
        | Halt false = Halt false => idtac
        | Loop = Loop => idtac

        | Halt true = Halt false => idtac
        | Halt false = Halt true => idtac
        | Halt _ = Loop => idtac
        | Loop = Halt _ => idtac
        | False => idtac
        | _ => fail
        end; inversion H
    end.

  Ltac run_simpl_rw := (
      rewrite decode_encode_prog_input_rw in * ||
      rewrite decode_encode_pair_rw in * ||
      rewrite encode_decode_pair_rw in * ||
      rewrite decode_encode_prog_rw in * ||
      rewrite encode_decode_prog_rw in *).


  Ltac run_simpl_norm :=
    match goal with
    | [ H: ?x = ?x |- _] => clear H
    | [ H1: Run ?m ?i ?r1, H2: Run ?m ?i ?r2  |- _] =>
      assert (r1 = r2) by eauto using run_fun;
      subst; clear H1
    | [ H: Halt _ = Halt _ |- _ ] => inversion H; subst; clear H
    | [ H1: Exec ?m ?i ?r1, H2: Exec ?m ?i ?r2  |- _] =>
      assert (r1 = r2) by eauto using exec_fun;
      subst; clear H1
    | [ H: true = _ |- _ ] => symmetry in H
    | [ H: false = _ |- _ ] => symmetry in H
    | [ H: Halt _ = _ |- _ ] => symmetry in H
    | [ H: Loop = _ |- _ ] => symmetry in H
    | [ H: negb _ = true |- _ ] => apply negb_true_iff in H; subst
    | [ H: negb _ = false |- _ ] => apply negb_false_iff in H; subst
    | [ H: andb _ _ = true |- _] => apply andb_prop in H
    | [ H: _ /\ _ |- _ ] => destruct H
    end.

  Ltac run_simpl :=
    run_simpl_rw ||
    run_simpl_explode ||
    run_simpl_norm ||
    run_simpl_inv.


  (** Simplify everything *)

  Ltac run_simpl_all := repeat run_simpl.

