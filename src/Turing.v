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
    | Accept
    | Reject
    | Loop.

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
  | With: input -> Prog -> Prog
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

  (**
    A decidable result is one that either accepts or rejects,
    never looping. *)
  Inductive Dec : result -> bool -> Prop :=
  | dec_accept:
    Dec Accept true
  | dec_reject:
    Dec Reject false.

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
  | run_with:
    forall p i j r,
    Run p i r ->
    Run (With i p) j r 
  | run_ret:
    (** We can directly return a result *)
    forall r i,
    Run (Ret r) i r
  | run_call:
    (** Calling a machine is the same as using function `run`. *)
    forall m i r,
    Exec m i r ->
    Run (Tur m) i r
  | run_seq_cont:
    (** If `p` terminates and returns `b`, then we can
       proceed with the execution of `q b`. *) 
    forall p q b r1 r2 i,
    Run p i r1 ->
    Dec r1 b ->
    Run (q b) i r2 ->
    Run (Seq p q) i r2
  | run_seq_loop:
    (** If `p` loops, then `p; q` also loops. *)
    forall p q i,
    Run p i Loop ->
    Run (Seq p q) i Loop
  | run_par_l_seq:
    (** If `p` terminates and `q` loops, then
       we run continuation `c` with `cleft b`. *)
    forall p q c r1 r2 b i,
    Run p i r1 ->
    Run q i Loop ->
    Dec r1 b ->
    Run (c (pleft b)) i r2 ->
    Run (Par p q c) i r2
  | run_par_r_seq:
    (** If `p` loops and `q` terminates, then
       we run continuation `c` with `cright b`. *)
    forall p q c r1 r2 b i,
    Run p i Loop ->
    Run q i r1 ->
    Dec r1 b ->
    Run (c (pright b)) i r2 ->
    Run (Par p q c) i r2
  | run_par_both:
    (** If both `p` and `q` terminate, then
       we run continuation `c` with `pboth b1 b2`. *)
    forall p1 p2 c r1 r2 r3 b1 b2 i,
    Run p1 i r1 ->
    Run p2 i r2 ->
    Dec r1 b1 ->
    Dec r2 b2 ->
    Run (c (par_choice p1 p2 b1 b2)) i r3 ->
    Run (Par p1 p2 c) i r3
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
  Notation ACCEPT := (Ret Accept).
  (** Notation for LOOP means returning Reject *)
  Notation REJECT := (Ret Reject).
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

  (** We use capital language to represent the recognized langauge of a machine.
      This corresponds to notation L(M). *)

  Definition Lang (p:Prog) : lang := fun i => Run p i Accept.

  (** We use a direct definition of recognition:
      The turing machine accepts input i (with `run m i`)
      iff language L accepts i.
       *)

  Definition Recognizes (p:Prog) (L:lang) :=
    forall i, Run p i Accept <-> L i.

  Lemma recognizes_def:
    forall p (L:lang),
    (forall i, Run p i Accept -> L i) ->
    (forall i, L i -> Run p i Accept) ->
    Recognizes p L.
  Proof.
    intros.
    unfold Recognizes.
    intros; split; auto.
  Qed.

  Lemma recognizes_to_equiv:
    forall m L,
    Recognizes m L ->
    Equiv (Lang m) L.
  Proof.
    intros.
    unfold Recognizes, Equiv, Lang in *.
    assumption.
  Qed.

  Lemma equiv_to_lang:
    forall m L,
    Equiv (Lang m) L ->
    Recognizes m L.
  Proof.
    intros.
    unfold Recognizes, Equiv, Lang in *.
    assumption.
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

  Lemma recognizes_iff_lang:
    forall m L,
    Equiv (Lang m) L <-> Recognizes m L.
  Proof.
    unfold Recognizes, Equiv, Lang in *.
    intuition.
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

  (*----------------------------------------------------------------------------*)

  Section RecognizesRun.

    Lemma dec_fun:
      forall r b1 b2,
      Dec r b1 ->
      Dec r b2 ->
      b1 = b2.
    Proof.
      intros.
      inversion H; subst; clear H;
      inversion H0; subst; clear H0; auto.
    Qed.

    Lemma dec_to_neq_loop:
      forall r b,
      Dec r b ->
      r <> Loop.
    Proof.
      intros.
      inversion H; subst; clear H; intros N; inversion N.
    Qed.

    Lemma neq_loop_to_dec:
      forall r,
      r <> Loop ->
      exists b, Dec r b.
    Proof.
      intros.
      destruct r.
      - exists true.
        apply dec_accept.
      - exists false.
        apply dec_reject.
      - contradiction.
    Qed.


    Ltac clear_dec :=
      match goal with
        | [ H1: Dec ?r ?b1, H2: Dec ?r ?b2 |- _] =>
          assert (Hx: b1 = b2) by eauto using dec_fun;
          rewrite Hx in *;
          clear H2 Hx
        | [ H: Dec Loop _ |- _ ] => inversion H
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
          ); subst; clear H2; try clear_dec; auto
        end;
        try clear_dec; auto.
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
        + assert (H := H true i).
          destruct H as (r, H).
          exists r.
          eapply run_seq_cont; eauto.
          constructor.
        + assert (H := H false i).
          destruct H as (r, H).
          exists r.
          eapply run_seq_cont; eauto.
          constructor.
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
        + assert (H := H (par_choice p1 p2 true true) i).
          destruct H as (r, Hr).
          exists r.
          eapply run_par_both; eauto using dec_accept.
        + assert (H := H (par_choice p1 p2 true false) i).
          destruct H as (r, Hr).
          exists r.
          eapply run_par_both; eauto using dec_accept, dec_reject.
        + assert (H := H (pleft true) i).
          destruct H as (r, Hr).
          exists r.
          eapply run_par_l_seq; eauto; constructor.
        + assert (H := H (par_choice p1 p2 false true) i).
          destruct H as (r, Hr).
          exists r.
          eapply run_par_both; eauto using dec_accept, dec_reject.
        + assert (H := H (par_choice p1 p2 false false) i).
          destruct H as (r, Hr).
          exists r.
          eapply run_par_both; eauto using dec_accept, dec_reject.
        + assert (H := H (pleft false) i).
          destruct H as (r, Hr).
          exists r.
          eapply run_par_l_seq; eauto; constructor.
        + assert (H := H (pright true) i).
          destruct H as (r, Hr).
          exists r.
          eapply run_par_r_seq; eauto; constructor.
        + assert (H := H (pright false) i).
          destruct H as (r, Hr).
          exists r.
          eapply run_par_r_seq; eauto; constructor.
        + exists Loop.
          constructor; auto.
    Qed.

    Lemma recognizes_run_reject:
      forall p L i,
      Recognizes p L ->
      Run p i Reject ->
      ~ L i.
    Proof.
      intros.
      intros N.
      apply H in N.
      assert (Hx: Reject = Accept) by eauto using run_fun.
      inversion Hx.
    Qed.

    Lemma recognizes_run_accept:
      forall p L,
      Recognizes p L ->
      forall i,
      Run p i Accept ->
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
      ~ Run p i Accept.
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
      Run p i Accept.
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
      assert (Hx: Loop = Accept) by eauto using run_fun.
      inversion Hx.
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
      Run m i Accept ->
      ~ L i.
    Proof.
      intros.
      apply recognizes_run_accept with (L:=compl L) in H0; auto.
    Qed.

    Lemma co_recognizes_not_accept:
      forall m L i,
      Recognizes m (compl L) ->
      L i ->
      ~ Run m i Accept.
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
      Run m i Accept.
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
    Definition Decider (d:Prog) := forall i, ~ Run d i Loop.

    Lemma decider_def:
      forall d,
      (forall i, ~ Run d i Loop) ->
      Decider d.
    Proof.
      intros.
      unfold Decider; intros.
      eauto.
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
      Run m i Reject ->
      ~ L i.
    Proof.
      intros.
      apply decides_to_recognizes in H.
      apply recognizes_run_reject with (p:=m); auto.
    Qed.

    Lemma decides_run_accept:
      forall m L i,
      Decides m L ->
      Run m i Accept ->
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
      Run m i Accept.
    Proof.
      intros.
      apply decides_to_recognizes in H.
      apply recognizes_accept with (L:=L); auto.
    Qed.

    Lemma decider_to_run:
      forall m,
      Decider m ->
      forall i,
      Run m i Accept \/ Run m i Reject.
    Proof.
      intros.
      unfold Decider in *.
      assert (H:=H i).
      destruct (run_exists m i) as (r, He);  auto.
      destruct r; auto.
      contradiction.
    Qed.

    Lemma decider_to_dec:
      forall m i r,
      Decider m ->
      Run m i r ->
      exists b, Dec r b.
    Proof.
      intros.
      apply decider_to_run with (i:=i) in H.
      assert (Hx: r = Accept \/ r = Reject). {
        intuition; eauto using run_fun.
      }
      destruct Hx;subst.
      - exists true.
        auto using dec_accept.
      - exists false.
        auto using dec_reject.
    Qed.

    Lemma decider_to_p_run:
      forall m,
      Decider m ->
      forall i,
      exists r b, Run m i r /\ Dec r b.
    Proof.
      intros.
      destruct (run_exists m i) as (r, He).
      exists r.
      assert (Hx : exists b, Dec r b) by eauto using decider_to_dec.
      destruct Hx as (b, Hx).
      eauto using run_call.
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
      Run m i Reject.
    Proof.
      intros.
      destruct H.
      apply decider_to_run with (i:=i) in H1.
      destruct H1.
      - apply recognizes_run_accept with (L:=L) in H1; auto.
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
      auto.
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

    Lemma decider_not_reject_to_accept:
      forall d i,
      Decider d ->
      ~ Run d i Reject ->
      Run d i Accept.
    Proof.
      intros.
      apply decider_no_loop with (i:=i) in H; eauto.
      destruct (run_exists d i) as ([], He); auto; contradiction.
    Qed.

  End Decidable.

  Definition halt_with (b:bool) := Ret (if b then Accept else Reject).

  Definition Empty : lang := fun p => False.
  Definition IsEmpty M := Recognizes M Empty.
  Definition NeverAccept M := (forall (i:input), ~ Run M i Accept).

  Section RUN.

    Lemma run_call_recognizes_accept:
      forall m L i,
      Recognizes m L ->
      L i ->
      Run m i Accept.
    Proof.
      intros.
      apply H; assumption.
    Qed.

    Lemma run_call_decides_accept:
      forall m L i,
      Decides m L ->
      L i ->
      Run m i Accept.
    Proof.
      intros.
      apply H.
      assumption.
    Qed.

    Lemma run_call_decides_reject:
      forall m L i,
      Decides m L ->
      ~ L i ->
      Run m i Reject.
    Proof.
      intros.
      eapply decides_reject; eauto.
    Qed.

    Lemma run_par_l_accept:
      forall i p q c r,
      Run p i Accept ->
      Run q i Loop ->
      Run (c (pleft true)) i r ->
      Run (Par p q c) i r.
    Proof.
      intros.
      apply run_par_l_seq with (r1:=Accept) (b:=true); auto.
      apply dec_accept.
    Qed.

    Lemma run_par_r_accept:
      forall i p q c r,
      Run q i Accept ->
      Run p i Loop ->
      Run (c (pright true)) i r ->
      Run (Par p q c) i r.
    Proof.
      intros.
      apply run_par_r_seq with (r1:=Accept) (b:=true); auto.
      apply dec_accept.
    Qed.

    Lemma run_par_l_reject:
      forall i p q c r,
      Run p i Reject ->
      Run q i Loop ->
      Run (c (pleft false)) i r ->
      Run (Par p q c) i r.
    Proof.
      intros.
      apply run_par_l_seq with (r1:=Reject) (b:=false); auto.
      apply dec_reject.
    Qed.

    Lemma run_par_r_reject:
      forall i p q c r,
      Run p i Loop ->
      Run q i Reject ->
      Run (c (pright false)) i r ->
      Run (Par p q c) i r.
    Proof.
      intros.
      apply run_par_r_seq with (r1:=Reject) (b:=false); auto.
      apply dec_reject.
    Qed.

    Lemma run_seq_reject:
      forall i p q r,
      Run p i Reject ->
      Run (q false) i r ->
      Run (Seq p q) i r.
    Proof.
      intros.
      apply run_seq_cont with (b:=false) (r1:=Reject).
      - assumption.
      - apply dec_reject.
      - assumption.
    Qed.

    Lemma run_seq_accept:
      forall i p q r,
      Run p i Accept ->
      Run (q true) i r ->
      Run (Seq p q) i r.
    Proof.
      intros.
      apply run_seq_cont with (b:=true) (r1:=Accept).
      - assumption.
      - apply dec_accept.
      - assumption.
    Qed.

    Lemma run_par_accept_reject:
      forall i p q c r,
      Run p i Accept ->
      Run q i Reject ->
      Run (c (par_choice p q true false)) i r ->
      Run (Par p q c) i r.
    Proof.
      intros.
      apply run_par_both with (r1:=Accept) (r2:=Reject) (b1:=true) (b2:=false);
      auto using dec_reject, dec_accept.
    Qed.

    Lemma run_halt_with_to_dec:
      forall i b r,
      Run (halt_with b) i r ->
      Dec r b.
    Proof.
      intros.
      inversion H; subst; clear H.
      destruct b.
      - apply dec_accept.
      - apply dec_reject.
    Qed.

    Lemma run_halt_with_inv_accept:
      forall i b,
      Run (halt_with b) i Accept ->
      b = true.
    Proof.
      intros.
      destruct b.
      - reflexivity.
      - inversion H.
    Qed.

    Lemma run_halt_with_inv_reject:
      forall i b,
      Run (halt_with b) i Reject ->
      b = false.
    Proof.
      intros.
      destruct b.
      - inversion H.
      - reflexivity.
    Qed.

    Lemma run_halt_with_true:
      forall i,
      Run (halt_with true) i Accept.
    Proof.
      apply run_ret.
    Qed.

    Lemma run_halt_with_false:
      forall i,
      Run (halt_with false) i Reject.
    Proof.
      apply run_ret.
    Qed.

  End RUN.


  (**
    A Theory to reason about recognizability/decidability directly on
    programs.
    *)
  Section P_DECIDER.
    Definition PAccepts (p:Prog) i := Run p i Accept.

    Lemma p_accepts_def:
      forall p i,
      Run p i Accept ->
      PAccepts p i.
    Proof.
      intros.
      auto.
    Qed.

    (* A program halts *)
    Definition PHalts p i := ~ Run p i Loop.

    Lemma p_halts_def:
      forall i r p,
      Run p i r ->
      r <> Loop ->
      PHalts p i.
    Proof.
      unfold PHalts; intros.
      intros N.
      assert (r = Loop) by eauto using run_fun.
      contradiction.
    Qed.

    Lemma p_halts_accept:
      forall p i,
      Run p i Accept ->
      PHalts p i.
    Proof.
      intros.
      apply p_halts_def with (r:=Accept).
      - assumption.
      - intros N; inversion N.
    Qed.

    Lemma p_halts_reject:
      forall p i,
      Run p i Reject ->
      PHalts p i.
    Proof.
      intros.
      apply p_halts_def with (r:=Reject).
      - assumption.
      - intros N; inversion N.
    Qed.

    Lemma p_halts_loop:
      forall p i,
      Run p i Loop ->
      ~ PHalts p i.
    Proof.
      intros.
      intros N.
      apply N in H.
      assumption.
    Qed.

    Lemma p_halts_ret_accept:
      forall i,
      PHalts (Ret Accept) i.
    Proof.
      intros.
      unfold PHalts.
      intros N.
      inversion N.
    Qed.

    Lemma p_halts_ret_reject:
      forall i,
      PHalts (Ret Reject) i.
    Proof.
      intros.
      unfold PHalts.
      intros N.
      inversion N.
    Qed.

    Lemma p_halts_dec:
      forall r b,
      Dec r b ->
      forall i,
      PHalts (Ret r) i.
    Proof.
      intros.
      apply p_halts_def with (r:=r).
      - apply run_ret.
      - apply dec_to_neq_loop in H.
        assumption.
    Qed.

    Lemma p_halts_seq:
      forall i p q r b,
      Run p i r ->
      Dec r b ->
      PHalts (q b) i ->
      PHalts (Seq p q) i.
    Proof.
      intros.
      intros N.
      inversion N; subst; clear N.
      + assert (r1 = r) by eauto using run_fun.
        subst.
        assert (b0 = b) by eauto using dec_fun.
        subst.
        apply H1; auto.
      + assert (r = Loop) by eauto using run_fun.
        subst.
        inversion H0.
    Qed.

    Inductive ParMerge p q : result -> result -> par_result -> Prop :=
    | par_merge_left:
      forall r b,
      Dec r b ->
      ParMerge p q r Loop (pleft b)
    | par_merge_right:
      forall r b,
      Dec r b ->
      ParMerge p q Loop r (pright b)
    | par_merge_both:
      forall r1 b1 r2 b2,
      Dec r1 b1 ->
      Dec r2 b2 ->
      ParMerge p q r1 r2 (par_choice p q b1 b2).

    Lemma par_merge_accept_accept p q:
      ParMerge p q Accept Accept (par_choice p q true true).
    Proof.
      auto using par_merge_both,dec_accept.
    Qed.

    Lemma par_merge_reject_accept p q:
      ParMerge p q Reject Accept (par_choice p q false true).
    Proof.
      auto using par_merge_both,dec_accept,dec_reject.
    Qed.

    Lemma par_merge_reject_reject p q:
      ParMerge p q Reject Reject (par_choice p q false false).
    Proof.
      auto using par_merge_both,dec_accept,dec_reject.
    Qed.

    Lemma par_merge_accept_reject p q:
      ParMerge p q Accept Reject (par_choice p q true false).
    Proof.
      auto using par_merge_both, dec_accept, dec_reject.
    Qed.

    Lemma par_merge_accept_loop p q:
      ParMerge p q Accept Loop (pleft true).
    Proof.
      auto using par_merge_left, dec_accept, dec_reject.
    Qed.

    Lemma par_merge_loop_accept p q:
      ParMerge p q Loop Accept (pright true).
    Proof.
      auto using par_merge_right, dec_accept, dec_reject.
    Qed.

    Lemma par_merge_reject_loop p q:
      ParMerge p q Reject Loop (pleft false).
    Proof.
      auto using par_merge_left, dec_accept, dec_reject.
    Qed.

    Lemma par_merge_loop_reject p q:
      ParMerge p q Loop Reject (pright false).
    Proof.
      auto using par_merge_right, dec_accept, dec_reject.
    Qed.

    Lemma p_halts_inv:
      forall p i,
      PHalts p i ->
      Run p i Accept \/ Run p i Reject.
    Proof.
      intros.
      unfold PHalts in *.
      destruct (run_exists p i) as (r, Hr).
      destruct r; auto.
      contradiction.
    Qed.

    Lemma p_halts_par_both:
      forall k p1 p2 b1 b2 r1 r2 i,
      Run p1 i r1 ->
      Run p2 i r2 ->
      Dec r1 b1 ->
      Dec r2 b2 ->
      PHalts (k (par_choice p1 p2 b1 b2)) i ->
      PHalts (Par p1 p2 k) i.
    Proof.
      intros.
      apply p_halts_inv in H3.
      intuition.
      - apply p_halts_accept.
        eapply run_par_both; eauto.
      - apply p_halts_reject.
        eapply run_par_both; eauto.
    Qed.

    Lemma p_halts_par_l_seq:
      forall k p1 p2 b r i,
      Run p1 i r ->
      Run p2 i Loop ->
      Dec r b ->
      PHalts (k (pleft b)) i ->
      PHalts (Par p1 p2 k) i.
    Proof.
      intros.
      apply p_halts_inv in H2.
      intuition.
      - apply p_halts_accept.
        eapply run_par_l_seq; eauto.
      - apply p_halts_reject.
        eapply run_par_l_seq; eauto.
    Qed.

    Lemma p_halts_par_r_seq:
      forall k p1 p2 b r i,
      Run p1 i Loop ->
      Run p2 i r ->
      Dec r b ->
      PHalts (k (pright b)) i ->
      PHalts (Par p1 p2 k) i.
    Proof.
      intros.
      apply p_halts_inv in H2.
      intuition.
      - apply p_halts_accept.
        eapply run_par_r_seq; eauto.
      - apply p_halts_reject.
        eapply run_par_r_seq; eauto.
    Qed.

    Lemma p_halts_par_l:
      forall i r1 b p1 p2 k,
      Run p1 i r1 ->
      Dec r1 b ->
      (forall r2 q, Run p2 i r2 -> ParMerge p1 p2 r1 r2 q -> PHalts (k q) i) ->
      PHalts (Par p1 p2 k) i.
    Proof.
      intros.
      inversion H0; subst; clear H0.
      - destruct (run_exists p2 i) as (r2, Hp2).
        intros N.
        destruct r2.
        + assert (Hp: PHalts (k (par_choice p1 p2 true true)) i). {
            apply H1 with (r2:=Accept); auto.
            apply par_merge_accept_accept.
          }
          eapply p_halts_par_both in Hp; eauto using dec_accept.
        + assert (Hp: PHalts (k (par_choice p1 p2 true false)) i). {
            apply H1 with (r2:=Reject); auto.
            apply par_merge_accept_reject.
          }
          eapply p_halts_par_both in Hp; eauto using dec_accept, dec_reject.
        + assert (Hp: PHalts (k (pleft true)) i). {
            apply H1 with (r2:=Loop); auto.
            apply par_merge_accept_loop.
          }
          eapply p_halts_par_l_seq in Hp; eauto using dec_accept.
      - destruct (run_exists p2 i) as (r2, Hp2).
        destruct r2.
        + assert (Hp: PHalts (k (par_choice p1 p2 false true)) i). {
            apply H1 with (r2:=Accept); auto.
            apply par_merge_reject_accept.
          }
          eapply p_halts_par_both in Hp; eauto using dec_accept, dec_reject.
        + assert (Hp: PHalts (k (par_choice p1 p2 false false)) i). {
            apply H1 with (r2:=Reject); auto.
            apply par_merge_reject_reject.
          }
          eapply p_halts_par_both in Hp; eauto using dec_accept, dec_reject.
        + assert (Hp: PHalts (k (pleft false)) i). {
            apply H1 with (r2:=Loop); auto.
            apply par_merge_reject_loop.
          }
          eapply p_halts_par_l_seq in Hp; eauto using dec_accept, dec_reject.
    Qed.

    Lemma p_halts_par_r:
      forall i r2 b p1 p2 k,
      Run p2 i r2 ->
      Dec r2 b ->
      (forall r1 q, Run p1 i r1 -> ParMerge p1 p2 r1 r2 q -> PHalts (k q) i) ->
      PHalts (Par p1 p2 k) i.
    Proof.
      intros.
      inversion H0; subst; clear H0.
      - destruct (run_exists p1 i) as (r1, Hp1).
        destruct r1.
        + assert (Hp: PHalts (k (par_choice p1 p2 true true)) i). {
            apply H1 with (r1:=Accept); auto.
            apply par_merge_accept_accept.
          }
          eapply p_halts_par_both in Hp; eauto using dec_accept, dec_reject.
        + assert (Hp: PHalts (k (par_choice p1 p2 false true)) i). {
            apply H1 with (r1:=Reject); auto.
            apply par_merge_reject_accept.
          }
          eapply p_halts_par_both in Hp; eauto using dec_accept, dec_reject.
        + assert (Hp: PHalts (k (pright true)) i). {
            apply H1 with (r1:=Loop); auto.
            apply par_merge_loop_accept.
          }
          eapply p_halts_par_r_seq in Hp; eauto using dec_accept.
      - destruct (run_exists p1 i) as (r1, Hp1).
        destruct r1.
        + assert (Hp: PHalts (k (par_choice p1 p2 true false)) i). {
            apply H1 with (r1:=Accept); auto.
            apply par_merge_accept_reject.
          }
          eapply p_halts_par_both in Hp; eauto using dec_accept, dec_reject.
        + assert (Hp: PHalts (k (par_choice p1 p2 false false)) i). {
            apply H1 with (r1:=Reject); auto.
            apply par_merge_reject_reject.
          }
          eapply p_halts_par_both in Hp; eauto using dec_accept, dec_reject.
        + assert (Hp: PHalts (k (pright false)) i). {
            apply H1 with (r1:=Loop); auto.
            apply par_merge_loop_reject.
          }
          eapply p_halts_par_r_seq in Hp; eauto using dec_accept, dec_reject.
    Qed.

    Lemma p_halts_tur:
      forall m i,
      ~ Exec m i Loop ->
      PHalts (Tur m) i.
    Proof.
      intros.
      destruct (exec_exists m i) as (r, He).
      apply p_halts_def with (r:=r); eauto using run_call.
      intros N.
      subst.
      contradiction.
    Qed.

    Lemma p_halts_call_decider:
      forall m i,
      Decider m ->
      PHalts m i.
    Proof.
      intros.
      assert (H := H i).
      destruct (run_exists m i) as (r, He).
      eapply p_halts_def; eauto.
      intros N.
      subst.
      contradiction.
    Qed.

    Lemma p_halts_seq_call:
      forall m i r k b,
      Exec m i r ->
      Dec r b ->
      PHalts (k b) i ->
      PHalts (Seq (Tur m) k) i.
    Proof.
      intros.
      apply p_halts_seq with (r:=r) (b:=b); auto using run_call.
    Qed.

    Lemma p_halts_seq_call_decider:
      forall m i k,
      Decider m ->
      (forall r b, Run m i r -> Dec r b -> PHalts (k b) i) ->
      PHalts (Seq m k) i.
    Proof.
      intros.
      destruct decider_to_p_run with (m:=m) (i:=i)
       as (r, (b, (Ha, Hb))); auto.
      apply p_halts_seq with (r:=r) (b:=b); auto.
      eauto.
    Qed.

    Lemma p_halts_halt_with:
      forall b i,
      PHalts (halt_with b) i.
    Proof.
      intros.
      apply p_halts_def with (r:=if b then Accept else Reject).
      - destruct b. {
          apply run_ret.
        }
        apply run_ret.
      - destruct b; intros N; inversion N.
    Qed.

    Definition PDecider (p:Prog) := forall i, PHalts p i.

    Lemma p_decider_def:
      forall p,
      (forall i, PHalts p i) ->
      PDecider p.
    Proof.
      intros.
      unfold PDecider.
      assumption.
    Qed.

    Lemma p_decider_to_decider:
      forall p,
      PDecider p ->
      Decider p.
    Proof.
      intros.
      unfold Decider.
      intros.
      assert (H := H i).
      apply H.
    Qed.

    Lemma p_halts_from_no_loop:
      forall p i,
      ~ Run p i Loop ->
      PHalts p i.
    Proof.
      intros.
      apply H.
    Qed.

    Lemma decider_to_p_decider:
      forall p,
      Decider p ->
      PDecider p.
    Proof.
      unfold PDecider, Decider.
      intros.
      assert (H := H i).
      auto using p_halts_from_no_loop.
    Qed.

    Lemma p_halts_seq_p_decider:
      forall p k,
      PDecider p ->
      forall i,
      (forall r b, Run p i r -> Dec r b -> PHalts (k b) i) ->
      PHalts (Seq p k) i.
    Proof.
      intros.
      apply p_decider_to_decider in H.
      apply decider_to_p_run with (i:=i) in H.
      destruct H as (r, (b, (Hr, Hd))).
      apply p_halts_seq with (r:=r) (b:=b); auto.
      eapply H0; eauto.
    Qed.

    Definition PDecides p L := Recognizes p L /\ PDecider p.

    Lemma p_decides_def:
      forall p L,
      Recognizes p L ->
      PDecider p ->
      PDecides p L.
    Proof.
      intros.
      unfold PDecides.
      auto.
    Qed.

    Lemma p_decides_to_decides:
      forall p L,
      PDecides p L ->
      Decides p L.
    Proof.
      intros.
      unfold Decides.
      destruct H.
      split.
      - assumption.
      - apply p_decider_to_decider.
        assumption.
    Qed.

    Lemma p_decides_to_p_recognizes:
      forall p L,
      PDecides p L ->
      Recognizes p L.
    Proof.
      intros.
      destruct H.
      assumption.
    Qed.

    Lemma p_decides_to_p_decider:
      forall p L,
      PDecides p L ->
      PDecider p.
    Proof.
      intros.
      destruct H; auto.
    Qed.

    Lemma p_decides_run_accept:
      forall p L i,
      PDecides p L ->
      Run p i Accept ->
      L i.
    Proof.
      intros.
      apply p_decides_to_p_recognizes in H.
      apply recognizes_run_accept with (p:=p); auto.
    Qed.

    Lemma p_decides_run_reject:
      forall p L i,
      PDecides p L ->
      Run p i Reject ->
      ~ L i.
    Proof.
      intros.
      apply p_decides_to_p_recognizes in H.
      eauto using recognizes_run_reject.
    Qed.

    Lemma p_decider_run_dec:
      forall p i r,
      PDecider p ->
      Run p i r ->
      exists b, Dec r b.
    Proof.
      intros.
      apply p_decider_to_decider in H.
      apply neq_loop_to_dec.
      intros N; subst.
      unfold Decider in *.
      apply H in H0; auto.
    Qed.

    Lemma p_decides_reject:
      forall p L i r,
      PDecides p L ->
      Run p i r ->
      ~ L i ->
      r = Reject.
    Proof.
      intros.
      destruct H as (Ha, Hb).
      apply recognizes_not_accept with (p:=p) in H1; auto.
      destruct r.
      - contradiction.
      - reflexivity.
      - apply p_decider_run_dec in H0; auto.
        destruct H0 as (b, H).
        inversion H.
    Qed.

    Lemma p_decides_accept:
      forall p L i r,
      PDecides p L ->
      Run p i r ->
      L i ->
      r = Accept.
    Proof.
      intros.
      apply p_decides_to_p_recognizes in H.
      eapply recognizes_accept in H1; eauto.
      eauto using run_fun.
    Qed.

    Lemma p_decidable_def:
      forall p L,
      PDecides p L ->
      Decidable L.
    Proof.
      intros.
      unfold Decidable.
      eauto using p_decides_to_decides.
    Qed.

    Lemma decidable_to_p_decides:
      forall L,
      Decidable L ->
      exists p, PDecides p L.
    Proof.
      intros.
      destruct H as (d, H).
      exists d.
      destruct H as (Ha, Hb).
      auto using p_decides_def, decider_to_p_decider.
    Qed.
  End P_DECIDER.

  Definition neg r :=
    match r with
    | Accept => Reject
    | Reject => Accept
    | Loop => Loop
    end.

  Lemma neg_accept_rw r:
    neg r = Accept <-> r = Reject.
  Proof.
    destruct r; simpl; split; auto; intros; inversion H.
  Qed.

  Lemma neg_reject_rw r:
    neg r = Reject <-> r = Accept.
  Proof.
    destruct r; simpl; split; auto; intros; inversion H.
  Qed.

  Lemma neg_loop_rw r:
    neg r = Loop <-> r = Loop.
  Proof.
    destruct r; simpl; split; auto; intros; inversion H.
  Qed.

  Lemma is_empty_never_accept_rw:
    forall M,
    IsEmpty M <-> NeverAccept M.
  Proof.
    unfold IsEmpty, NeverAccept; split; intros.
    - intros N; subst.
      apply H in N.
      unfold Empty in *.
      assumption.
    - unfold Recognizes.
      split; intros. {
        apply H in H0.
        contradiction.
      }
      inversion H0.
  Qed.

  (** Tactics that simplify `Run` objects in the assumptions. *)

  Ltac run_simpl_inv :=
  match goal with
  | [ H: _ |- _ ] =>
    match type of H with
      | Run (With _ _) _ _ => idtac
      | Run (Read _) _ _ => idtac
      | Run (Tur _) _ _ => idtac
      | Run (Ret _) _ _ => idtac
      | Dec _ true => idtac
      | Dec _ false => idtac
      | Dec Accept _ => idtac
      | Dec Reject _ => idtac
      | Dec Loop _ => idtac
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
        | Accept = Reject => idtac
        | Accept = Loop => idtac
        | Reject = Accept => idtac
        | Reject = Loop => idtac
        | Loop = Accept => idtac
        | Loop = Reject => idtac
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
    | [ H1: Exec ?m ?i ?r1, H2: Exec ?m ?i ?r2  |- _] =>
      assert (r1 = r2) by eauto using exec_fun;
      subst; clear H1
    | [ H: Run (halt_with _) _ _ |- _ ] => apply run_halt_with_to_dec in H
    | [ H: true = _ |- _ ] => symmetry in H
    | [ H: false = _ |- _ ] => symmetry in H
    | [ H: Reject = _ |- _ ] => symmetry in H
    | [ H: Loop = _ |- _ ] => symmetry in H
    | [ H: Accept = _ |- _ ] => symmetry in H
    | [ H: negb _ = true |- _ ] => apply negb_true_iff in H; subst
    | [ H: negb _ = false |- _ ] => apply negb_false_iff in H; subst
    | [ H: andb _ _ = true |- _] => apply andb_prop in H
    | [ H: _ /\ _ |- _ ] => destruct H
    | [ H: neg _ = Accept |- _ ] => apply neg_accept_rw in H
    | [ H: neg _ = Reject |- _ ] => apply neg_reject_rw in H
    | [ H: neg _ = Loop |- _ ] => apply neg_loop_rw in H
    end.

  Ltac run_simpl :=
    run_simpl_rw ||
    run_simpl_explode ||
    run_simpl_norm ||
    run_simpl_inv.


  (** Simplify everything *)

  Ltac run_simpl_all := repeat run_simpl.

