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

  (** We can run a machine and obtain its run result. *)
  Parameter Exec: machine -> input -> bool -> Prop.

  Parameter exec_fun: forall m i b1 b2,
    Exec m i b1 ->
    Exec m i b2 ->
    b1 = b2.

  Parameter exec_exists:
    forall m i,
    (exists b, Exec m i b) \/ (forall b, ~ Exec m i b).

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
  | Ret: bool -> Prog
  .

  (**
    These describe the axiomatic semantics of turing machines.
    We can run a program `p` and obtain a resul `r` with
    `Run p r`.
    *)
  Inductive Run: Prog -> input -> bool -> Prop :=
  | run_read:
    forall p i b,
    Run (p i) i b->
    Run (Read p) i b
  | run_call:
    forall p i j b,
    Run p i b ->
    Run (Call p i) j b 
  | run_ret:
    (** We can directly return a result *)
    forall b i,
    Run (Ret b) i b
  | run_tur:
    (** Run a turing machine `m`. *)
    forall m i b,
    Exec m i b ->
    Run (Tur m) i b
  | run_seq:
    (** If `p` terminates and returns `b`, then we can
       proceed with the execution of `q b`. *) 
    forall p q b1 b2 i,
    Run p i b1 ->
    Run (q b1) i b2 ->
    Run (Seq p q) i b2.

  Inductive Halt : Prog -> input -> Prop :=
  | halt_read:
    forall p i,
    Halt (p i) i ->
    Halt (Read p) i
  | halt_call:
    forall p i j,
    Halt p i ->
    Halt (Call p i) j 
  | halt_ret:
    (** We can directly return a result *)
    forall i b,
    Halt (Ret b) i
  | halt_tur:
    (** Run a turing machine `m`. *)
    forall m i b,
    Exec m i b ->
    Halt (Tur m) i
  | halt_seq:
    (** If `p` terminates and returns `b`, then we can
       proceed with the execution of `q b`. *) 
    forall p q b i,
    Run p i b ->
    Halt (q b) i ->
    Halt (Seq p q) i.

  Inductive Loop: Prog -> input -> Prop :=
  | loop_read:
    forall p i,
    Loop (p i) i ->
    Loop (Read p) i
  | loop_call:
    forall p i j,
    Loop p i ->
    Loop (Call p i) j
  | loop_tur:
    (** Run a turing machine `m`. *)
    forall m i,
    (forall b, ~ Exec m i b) ->
    Loop (Tur m) i
  | loop_seq_l:
    (** If `p` terminates and returns `b`, then we can
       proceed with the execution of `q b`. *) 
    forall p q i,
    Loop p i ->
    Loop (Seq p q) i
  | loop_seq_r:
    (** If `p` terminates and returns `b`, then we can
       proceed with the execution of `q b`. *) 
    forall p q b i,
    Run p i b ->
    Loop (q b) i ->
    Loop (Seq p q) i.

  Inductive Negative p i : Prop :=
  | negative_run_false:
    Run p i false ->
    Negative p i
  | negative_loop:
    Loop p i ->
    Negative p i.

  (** We define a notation for sequencing. *)
  Notation "'mlet' x <- e 'in' c" := (Seq e (fun x => c)) (at level 60, right associativity).

  Lemma run_read_rw:
    forall f i b,
    Run (Read f) i b <-> Run (f i) i b.
  Proof.
    split; intros.
    - inversion H; subst; auto.
    - constructor; assumption.
  Qed.

  Lemma run_call_rw:
    forall p i j b,
    Run (Call p j) i b <-> Run p j b.
  Proof.
    split; intros.
    - inversion H; subst; auto.
    - constructor; auto.
  Qed.

  Lemma halt_read_rw:
    forall f i,
    Halt (Read f) i <-> Halt (f i) i.
  Proof.
    split; intros.
    - inversion H; subst; auto.
    - constructor; assumption.
  Qed.

  Lemma halt_call_rw:
    forall p i j,
    Halt (Call p j) i <-> Halt p j.
  Proof.
    split; intros.
    - inversion H; subst; auto.
    - constructor; auto.
  Qed.

  (*----------------------------------------------------------------------------*)

  Section RunLoopHalt.

    Lemma run_fun:
      forall p i b1,
      Run p i b1 ->
      forall b2,
      Run p i b2 ->
      b1 = b2.
    Proof.
      intros p i r1 H; induction H; intros r' He;
        inversion He; subst; clear He; auto;
        (* In each case we have a bunch of Run's that are solved
           by induction; we need to make sure we clear any dec's,
           so that we can advance to the next IH *) 
        repeat match goal with
        | [ H1: Run ?q i ?b1, H2: Run ?q i ?b2 |- _] =>
          (
            assert (b1 = b2) by eauto ||
            assert (b2 = b1) by eauto
          ); subst; clear H2; auto
        end;
        auto.
      eauto using exec_fun.
    Qed.

    Lemma halt_to_run:
      forall p i,
      Halt p i ->
      exists b, Run p i b.
    Proof.
      intros.
      induction H; try destruct IHHalt as (b, Hr).
      - exists b.
        constructor.
        assumption.
      - exists b.
        constructor.
        assumption.
      - exists b.
        constructor.
      - exists b.
        constructor.
        assumption.
      - destruct IHHalt as (b1, Hr).
        exists b1.
        econstructor; eauto.
    Qed.

    Lemma run_to_halt:
      forall p i b,
      Run p i b ->
      Halt p i.
    Proof.
      intros.
      induction H.
      - constructor.
        assumption.
      - constructor.
        assumption.
      - constructor.
      - eapply halt_tur; eauto.
      - eapply halt_seq; eauto.
    Qed.

    Lemma halt_rw:
      forall p i,
      Halt p i <-> exists b, Run p i b.
    Proof.
      split; intros.
      - auto using halt_to_run.
      - destruct H.
        eauto using run_to_halt.
    Qed.

    Lemma halt_or_loop:
      forall p i,
      Halt p i \/ Loop p i.
    Proof.
      induction p; intros.
      - assert (H := H i i).
        destruct H as [H| H].
        + left.
          constructor.
          assumption.
        + right.
          constructor.
          assumption.
      - assert (IHp := IHp i).
        destruct IHp as [H|H]. {
          left.
          constructor.
          assumption.
        }
        right.
        constructor.
        assumption.
      - assert (IHp := IHp i).
        destruct IHp as [IH|IH].
        + apply halt_to_run in IH.
          destruct IH as (b, IH).
          assert (H := H b i).
          destruct H as [H|H]. {
            left.
            econstructor; eauto.
          }
          right.
          eapply loop_seq_r; eauto.
        + right.
          eauto using loop_seq_l.
      - destruct (exec_exists m i) as [(b, He)|Hl]. {
          left.
          econstructor.
          eauto.
        }
        right.
        constructor.
        auto.
      - left.
        constructor.
    Qed.

    Lemma loop_to_not_halt:
      forall p i,
      Loop p i ->
      ~ Halt p i.
    Proof.
      intros; induction H; intros N; inversion_clear N;
        try (contradict IHLoop; auto; fail).
      - apply H in H0.
        assumption.
      - contradict IHLoop.
        eapply run_to_halt; eauto.
      - assert (b0 = b) by eauto using run_fun.
        subst.
        contradiction.
    Qed.

    Lemma halt_to_not_loop:
      forall p i,
      Halt p i ->
      ~ Loop p i.
    Proof.
      intros.
      induction H; intros N.
      - inversion_clear N.
        contradict H.
        auto.
      - inversion_clear N.
        contradiction.
      - inversion_clear N.
      - inversion_clear N.
        contradict H.
        auto.
      - inversion_clear N. {
          apply loop_to_not_halt in H1.
          contradict H1.
          eapply run_to_halt; eauto.
        }
        assert (b0 = b) by eauto using run_fun.
        subst.
        contradiction.
    Qed.

    Lemma not_halt_to_loop:
      forall p i,
      ~ Halt p i ->
      Loop p i.
    Proof.
      intros.
      destruct (halt_or_loop p i). {
        contradiction.
      }
      assumption.
    Qed.

    Lemma loop_rw:
      forall p i,
      Loop p i <-> ~ Halt p i.
    Proof.
      split; intros. {
        auto using loop_to_not_halt.
      }
      auto using not_halt_to_loop.
    Qed.

    Lemma loop_read_rw:
      forall p i,
      Loop (Read p) i <-> Loop (p i) i.
    Proof.
      split; intros. {
        inversion_clear H.
        assumption.
      }
      auto using loop_read.
    Qed.

    Lemma loop_call_rw:
      forall p i j,
      Loop (Call p j) i <-> Loop p j.
    Proof.
      split; intros. {
        inversion_clear H.
        assumption.
      }
      auto using loop_call.
    Qed.

    Lemma run_exists:
      forall p i,
      (exists b, Run p i b) \/ Loop p i.
    Proof.
      intros.
      destruct (halt_or_loop p i); auto.
      rewrite halt_rw in *.
      auto.
    Qed.

    Lemma loop_alt_rw:
      forall p i,
      Loop p i <-> (forall b, ~ Run p i b).
    Proof.
      split; intros. {
        rewrite loop_rw in H.
        intros N.
        contradict H.
        eauto using run_to_halt.
      }
      rewrite loop_rw.
      intros N.
      rewrite halt_rw in N.
      destruct N as (b, N).
      apply H in N.
      contradiction.
    Qed.

    Lemma negative_alt_rw:
      forall p i,
      Negative p i <-> (Run p i false \/ Loop p i).
    Proof.
      split; intros. { inversion_clear H; auto. }
      destruct H. { auto using negative_run_false. }
      auto using negative_loop.
    Qed.

    Lemma negative_rw:
      forall p i,
      Negative p i <-> ~ Run p i true.
    Proof.
      split; intros. {
        intros N.
        inversion_clear H. {
          assert (X: true = false) by eauto using run_fun.
          inversion X.
        }
        rewrite loop_rw in *.
        contradict H0.
        eapply run_to_halt; eauto.
      }
      destruct (halt_or_loop p i). {
        rewrite halt_rw in *.
        destruct H0 as ([], Ha); try contradiction.
        auto using negative_run_false.
      }
      auto using negative_loop.
    Qed.

    Lemma negative_read_rw:
      forall p i,
      Negative (Read p) i <-> Negative (p i) i.
    Proof.
      split; intros. {
        inversion_clear H. {
          rewrite run_read_rw in *.
          auto using negative_run_false.
        }
        rewrite loop_read_rw in *.
        auto using negative_loop.
      }
      rewrite negative_alt_rw in H.
      destruct H. {
        apply negative_run_false.
        rewrite run_read_rw.
        assumption.
      }
      apply negative_loop.
      rewrite loop_read_rw.
      assumption.
    Qed.

    Lemma negative_call_rw:
      forall p i j,
      Negative (Call p j) i <-> Negative p j.
    Proof.
      split; intros. {
        inversion_clear H. {
          rewrite run_call_rw in *.
          auto using negative_run_false.
        }
        rewrite loop_call_rw in *.
        auto using negative_loop.
      }
      rewrite negative_alt_rw in H.
      destruct H. {
        apply negative_run_false.
        rewrite run_call_rw.
        assumption.
      }
      apply negative_loop.
      rewrite loop_call_rw.
      assumption.
    Qed.

    Lemma run_true_or_negative:
      forall p i,
      Run p i true \/ Negative p i.
    Proof.
      intros.
      destruct (run_exists p i) as [([], H)|H];
        auto;
        right;
        auto using negative_run_false, negative_loop.
    Qed.

  End RunLoopHalt.

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
    forall i, Run p i true <-> L i.

  Lemma recognizes_def:
    forall p (L:lang),
    (forall i, Run p i true -> L i) ->
    (forall i, L i -> Run p i true) ->
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

  Section RecognizesRun.

    Lemma recognizes_run_reject:
      forall p L i,
      Recognizes p L ->
      Run p i false ->
      ~ L i.
    Proof.
      intros.
      intros N.
      apply H in N.
      assert (Hx: true = false) by eauto using run_fun.
      inversion Hx.
    Qed.

    Lemma recognizes_run_accept:
      forall p L,
      Recognizes p L ->
      forall i,
      Run p i true ->
      L i.
    Proof.
      intros.
      apply H.
      assumption.
    Qed.


    Lemma recognizes_not_accept:
      forall p L,
      Recognizes p L ->
      forall i,
      ~ L i ->
      ~ Run p i true.
    Proof.
      intros.
      intros N.
      assert (L i). { eapply recognizes_run_accept; eauto. }
      contradiction.
    Qed.

    Lemma recognizes_negative:
      forall p L,
      Recognizes p L ->
      forall i,
      ~ L i ->
      Negative p i.
    Proof.
      intros.
      rewrite negative_rw.
      eauto using recognizes_not_accept.
    Qed.

    Lemma recognizes_accept:
      forall p L i,
      Recognizes p L ->
      L i ->
      Run p i true.
    Proof.
      intros.
      apply H in H0.
      assumption.
    Qed.

    Lemma recognizes_run_loop:
      forall p L,
      Recognizes p L ->
      forall i,
      Loop p i ->
      ~ L i.
    Proof.
      intros.
      intros N.
      apply H in N.
      apply halt_to_not_loop in H0; auto.
      eauto using run_to_halt.
    Qed.

    Lemma recognizes_inv_negative:
      forall p L,
      Recognizes p L ->
      forall i,
      Negative p i ->
      ~ L i.
    Proof.
      intros.
      inversion_clear H0.
      - eauto using recognizes_run_reject.
      - eauto using recognizes_run_loop.
    Qed.

    Lemma recognizes_accept_rw:
      forall p L,
      Recognizes p L ->
      forall i,
      Run p i true <-> L i.
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
      Run m i true ->
      ~ L i.
    Proof.
      intros.
      apply recognizes_run_accept with (L:=compl L) in H0; auto.
    Qed.

    Lemma co_recognizes_not_accept:
      forall m L i,
      Recognizes m (compl L) ->
      L i ->
      ~ Run m i true.
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
      Run m i true.
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

    Definition Decider (p:Prog) := forall i, Halt p i.

    Lemma decider_def:
      forall p,
      (forall i, Halt p i) ->
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
      Run m i false ->
      ~ L i.
    Proof.
      intros.
      apply decides_to_recognizes in H.
      apply recognizes_run_reject with (p:=m); auto.
    Qed.

    Lemma decides_run_accept:
      forall m L i,
      Decides m L ->
      Run m i true ->
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
      Run m i true.
    Proof.
      intros.
      apply decides_to_recognizes in H.
      apply recognizes_accept with (L:=L); auto.
    Qed.

    Lemma decider_to_halt:
      forall p,
      Decider p ->
      forall i,
      Halt p i.
    Proof.
      intros.
      unfold Decider in *.
      auto.
    Qed.

    Lemma decider_to_run:
      forall p i,
      Decider p ->
      exists b, Run p i b.
    Proof.
      intros.
      apply decider_to_halt with (i:=i) in H.
      rewrite halt_rw in *.
      assumption.
    Qed.

    Lemma decides_to_run:
      forall p L i,
      Decides p L ->
      exists b, Run p i b.
    Proof.
      intros.
      destruct H.
      specialize (H0 i).
      rewrite halt_rw in *.
      assumption.
    Qed.

    Lemma decides_to_halt:
      forall p L,
      Decides p L ->
      forall i,
      Halt p i.
    Proof.
      intros.
      destruct H.
      unfold Decider in *.
      auto.
    Qed.

    Lemma decider_to_not_loop:
      forall p,
      Decider p ->
      forall i,
      ~ Loop p i.
    Proof.
      intros.
      specialize (H i).
      auto using halt_to_not_loop.
    Qed.

    Lemma decider_not_reject:
      forall p i,
      Decider p ->
      ~ Run p i false ->
      Run p i true.
    Proof.
      intros.
      assert (H := H i).
      rewrite halt_rw in *.
      destruct H as (b, H).
      destruct b;
      intuition.
    Qed.

    Lemma decider_not_accept:
      forall m i,
      Decider m ->
      ~ Run m i true ->
      Run m i false.
    Proof.
      intros.
      assert (H := H i).
      rewrite halt_rw in *.
      destruct H as (b, H).
      destruct b;
      intuition.
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
      Run m i false.
    Proof.
      intros.
      destruct H.
      assert (Ha: Halt m i) by auto using decider_to_halt.
      rewrite halt_rw in *.
      destruct Ha as (b, Ha).
      destruct b; auto.
      contradict H0.
      eapply recognizes_run_accept; eauto.
    Qed.

    Lemma halt_seq_decider:
      forall p i j (c:bool -> Prog),
      Decider p ->
      (forall (b:bool), Run p j b -> Halt (c b) i) -> 
      Halt (Seq (Call p j) c) i.
    Proof.
      intros.
      destruct decider_to_run with (i:=j)
        (p:=p) as (b,Ha); auto.
      apply halt_seq with (b:=b); auto.
      constructor.
      assumption.
    Qed.

    Lemma halt_seq_decides:
      forall p i j L (c:bool -> Prog),
      Decides p L ->
      (forall (b:bool), Run p j b -> Halt (c b) i) -> 
      Halt (Seq (Call p j) c) i.
    Proof.
      intros.
      apply halt_seq_decider; auto.
      destruct H; auto.
    Qed.

  End Decidable.


  (** Tactics that simplify `Run` objects in the assumptions. *)

  Ltac run_simpl_inv :=
  match goal with
  | [ H: _ |- _ ] =>
    match type of H with
      | Run (Call _ _) _ _ => idtac
      | Run (Read _) _ _ => idtac
      | Run (Tur _) _ _ => idtac
      | Run (Ret _) _ _ => idtac
      | Loop (Call _ _) _ => idtac
      | Loop (Read _) _ => idtac
      | Loop (Tur _) _ => idtac
      | Loop (Ret _) _ => idtac
      | Halt (Call _ _) _ => idtac
      | Halt (Read _) _ => idtac
      | Halt (Tur _) _ => idtac
      | Halt (Ret _) _ => idtac
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
    | [ H1: Negative ?p ?i, H2: Run ?p ?i true |- _ ] =>
      rewrite negative_rw in H1; contradiction
    | [ H1: Run ?p ?i _, H2: Loop ?p ?i |- _ ] =>
      apply run_to_halt in H1;
      rewrite loop_rw in H2; contradiction 
    | [ H1: Halt ?p ?i, H2: Loop ?p ?i |- _ ] =>
      rewrite loop_rw in H2; contradiction
    | [ H1: Run ?m ?i ?r1, H2: Run ?m ?i ?r2  |- _] =>
      assert (r1 = r2) by eauto using run_fun;
      subst; clear H1
    | [ H1: Exec ?m ?i ?r1, H2: Exec ?m ?i ?r2  |- _] =>
      assert (r1 = r2) by eauto using exec_fun;
      subst; clear H1
    | [ H: true = _ |- _ ] => symmetry in H
    | [ H: false = _ |- _ ] => symmetry in H
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
