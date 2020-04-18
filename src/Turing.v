Require Import Coq.Setoids.Setoid.
Require Import Coq.Bool.Bool.
Require Import Coq.Logic.Classical_Prop.

Module Type Turing.
  (** These are the assumptions of our theory: *)
  (** We leave the input and the machine as unspecified data types. *)
  Parameter input: Type.
  (** Equality over the input is decidable. *)
  Parameter input_eq_dec: forall x y: input, {x = y} + {x <> y}.
  Parameter machine: Type.

  (** We also define a function to serialize a machine into a string (of type
      input). In the book, this corresponds to notation <M>. *)
  Parameter encode_machine: machine -> input.
  (** Similarly, we have a function that takes a string and produces a machine.
      In the book, this corresponds to notation M = <M> *)
  Parameter decode_machine: input -> machine.
  (** Decoding and encoding a machine yields the same machine. *)
  Axiom decode_encode_machine_rw:
    forall m,
    decode_machine (encode_machine m) = m.
  (** Let us say we have a function that can encode and decode a pair of
      inputs. *)
  Parameter decode_pair : input -> (input * input).
  Parameter encode_pair: (input * input) -> input.
  Axiom decode_encode_pair_rw:
    forall p,
    decode_pair (encode_pair p) = p.

  (** Let us define an abbreviation of the above functions. *)
  Notation "'<<' w1 ',' w2 '>>'" := (encode_pair w1 w2).
  Notation "'[[' M ']]'" := (encode_machine M).


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
  Parameter run: machine -> input -> result.
  (** When running two programs in parallel, we get to know
      which of the two programs has terminated and how they
      terminated. *)
  Inductive par_result :=
  | pleft: bool -> par_result
  | pright: bool -> par_result
  | pboth: bool -> bool -> par_result.

  Inductive Prog :=
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
  | Call: machine -> input -> Prog
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

  (**
    These describe the axiomatic semantics of turing machines.
    We can run a program `p` and obtain a resul `r` with
    `Run p r`.
    *)
  Inductive Run: Prog -> result -> Prop :=
  | run_ret:
    (** We can directly return a result *)
    forall r,
    Run (Ret r) r
  | run_call:
    (** Calling a machine is the same as using function `run`. *)
    forall m i,
    Run (Call m i) (run m i)
  | run_seq_cont:
    (** If `p` terminates and returns `b`, then we can
       proceed with the execution of `q b`. *) 
    forall p q b r1 r2,
    Run p r1 ->
    Dec r1 b ->
    Run (q b) r2 ->
    Run (Seq p q) r2
  | run_seq_loop:
    (** If `p` loops, then `p; q` also loops. *)
    forall p q,
    Run p Loop ->
    Run (Seq p q) Loop
  | run_par_l_seq:
    (** If `p` terminates and `q` loops, then
       we run continuation `c` with `cleft b`. *)
    forall p q c r1 r2 b,
    Run p r1 ->
    Run q Loop ->
    Dec r1 b ->
    Run (c (pleft b)) r2 ->
    Run (Par p q c) r2
  | run_par_r_seq:
    (** If `p` loops and `q` terminates, then
       we run continuation `c` with `cright b`. *)
    forall p q c r1 r2 b,
    Run p Loop ->
    Run q r1 ->
    Dec r1 b ->
    Run (c (pright b)) r2 ->
    Run (Par p q c) r2
  | run_par_both:
    (** If both `p` and `q` terminate, then
       we run continuation `c` with `pboth b1 b2`. *)
    forall p q c r1 r2 r3 b1 b2,
    Run p r1 ->
    Run q r2 ->
    Dec r1 b1 ->
    Dec r2 b2 ->
    Run (c (pboth b1 b2)) r3 ->
    Run (Par p q c) r3
  | run_par_loop:
    (** If both `p` and `q` loop, then the whole thing loops. *)
    forall p q c,
    Run p Loop ->
    Run q Loop ->
    Run (Par p q c) Loop.
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
  (** We leave unspecified how we convert a program to a Turing machine. *)
  Parameter Build : (input -> Prog) -> machine.
  (** We specify the behavior of `Build` *)
  Axiom run_build: forall p i r, Run (p i) r <-> run (Build p) i = r.
End Turing.

Module TuringBasics (Tur : Turing).
  Import Tur.

  (** Given a machine and a string, encodes the pair as a string.
      In the book, this corresponds to notation <M, w>. *)
  Definition encode_machine_input (M:machine) (w:input) : input :=
    encode_pair (encode_machine M, w).

  (** Given a string this function deserializes a pair M and w, given an encoded
      string <M,w>. *)
  Definition decode_machine_input p := let (M, w) :=
    decode_pair p in (decode_machine M, w).

  Notation "'<[' M , w ']>'" := (encode_machine_input M w).

  (** Decoding and encoding a pair yields the same pair. *)
  Lemma decode_encode_machine_input_rw:
    forall M w,
    decode_machine_input
          (encode_machine_input M w) = (M, w).
  Proof.
    intros.
    unfold decode_machine_input.
    unfold encode_machine_input.
    rewrite decode_encode_pair_rw.
    rewrite decode_encode_machine_rw.
    reflexivity.
  Qed.

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

  Definition Lang (m:machine) : lang := fun i => run m i = Accept.

  (** We use a direct definition of recognition:
      The turing machine accepts input i (with `run m i`)
      iff language L accepts i.
       *)

  Definition Recognizes (m:machine) (L:lang) :=
    forall i, run m i = Accept <-> L i.

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

  Definition Recognizable (L:lang) : Prop := exists m, Recognizes m L.

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

    Lemma recognizes_run_reject:
      forall m L i,
      Recognizes m L ->
      run m i = Reject ->
      ~ L i.
    Proof.
      intros.
      intros N.
      apply H in N.
      rewrite N in *.
      inversion H0.
    Qed.

    Lemma recognizes_run_accept:
      forall m L,
      Recognizes m L ->
      forall i,
      run m i = Accept ->
      L i.
    Proof.
      intros.
      apply H.
      assumption.
    Qed.


    Lemma recognizes_not_accept:
      forall m L i,
      Recognizes m L ->
      ~ L i ->
      run m i <> Accept.
    Proof.
      intros.
      intros N.
      apply recognizes_run_accept with (L:=L) in N; auto.
    Qed.

    Lemma recognizes_accept:
      forall m L i,
      Recognizes m L ->
      L i ->
      run m i = Accept.
    Proof.
      intros.
      apply H in H0.
      assumption.
    Qed.

    Lemma recognizes_run_loop:
      forall m L,
      Recognizes m L ->
      forall i,
      run m i = Loop ->
      ~ L i.
    Proof.
      intros.
      intros N.
      apply H in N.
      rewrite N in *.
      inversion H0.
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
      run m i = Accept ->
      ~ L i.
    Proof.
      intros.
      apply recognizes_run_accept with (L:=compl L) in H0; auto.
    Qed.

    Lemma co_recognizes_not_accept:
      forall m L i,
      Recognizes m (compl L) ->
      L i ->
      run m i <> Accept.
    Proof.
      intros.
      intros N.
      apply recognizes_run_accept with (L:=compl L) in N; auto.
    Qed.

    Lemma co_recognizes_accept:
      forall m L i,
      Recognizes m (compl L) ->
      ~ L i ->
      run m i = Accept.
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
    Definition Decider d := forall i, run d i <> Loop.

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
      run m i = Reject ->
      ~ L i.
    Proof.
      intros.
      apply decides_to_recognizes in H.
      apply recognizes_run_reject with (m:=m); auto.
    Qed.

    Lemma decides_run_accept:
      forall m L i,
      Decides m L ->
      run m i = Accept ->
      L i.
    Proof.
      intros.
      apply decides_to_recognizes in H.
      apply recognizes_run_accept with (m:=m); auto.
    Qed.

    Lemma decides_accept:
      forall m L i,
      Decides m L ->
      L i ->
      run m i = Accept.
    Proof.
      intros.
      apply decides_to_recognizes in H.
      apply recognizes_accept with (L:=L); auto.
    Qed.

    Lemma decider_to_run:
      forall m,
      Decider m ->
      forall i,
      run m i = Accept \/ run m i = Reject.
    Proof.
      intros.
      unfold Decider in *.
      assert (H:=H i).
      destruct (run m i); auto.
      contradiction.
    Qed.

    Lemma decides_reject:
      forall m L i,
      Decides m L ->
      ~ L i ->
      run m i = Reject.
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
      run m i <> Loop.
    Proof.
      intros.
      intros N.
      unfold Decider in *.
      assert (H := H i).
      contradiction.
    Qed.

    Lemma decides_no_loop:
      forall m L i,
      Decides m L ->
      run m i <> Loop.
    Proof.
      intros.
      destruct H.
      apply decider_no_loop.
      assumption.
    Qed.

    Lemma decider_not_reject_to_accept:
      forall d i,
      Decider d ->
      run d i <> Reject ->
      run d i = Accept.
    Proof.
      intros.
      apply decider_no_loop with (i:=i) in H.
      destruct (run d i).
      - trivial.
      - contradiction.
      - contradiction.
    Qed.

    Definition Predicate M f :=
      (forall w, run M w = Accept <-> f w = true) /\
      (forall w, run M w = Reject <-> f w = false). 

    Lemma decider_to_predicate:
      forall M L,
      Decides M L ->
      exists f, Predicate M f.
    Proof.
      intros.
      exists (fun w =>
        match run M w with
        | Accept => true
        | _ => false
        end).
      unfold Predicate.
      split; split; intros.
      - rewrite H0.
        reflexivity.
      - destruct (run M w); auto; inversion H0.
      - rewrite H0.
        reflexivity.
      - destruct (run M w) eqn:Hr; auto; inversion H0.
        apply H in Hr.
        contradiction.
    Qed.

    Lemma predicate_accept:
      forall M f w,
      Predicate M f ->
      run M w = Accept <-> f w = true.
    Proof.
      intros.
      destruct H as (H1, H2).
      auto.
    Qed.

    Lemma predicate_reject:
      forall M f w,
      Predicate M f ->
      run M w = Reject <-> f w = false.
    Proof.
      intros.
      destruct H as (H1, H2).
      auto.
    Qed.

  End Decidable.

  Definition halt_with (b:bool) := Ret (if b then Accept else Reject).

  Definition Empty : lang := fun p => False.
  Definition IsEmpty M := Recognizes M Empty.
  Definition NeverAccept M := (forall w, run M w <> Accept).

  Section RUN.

    Lemma run_call_eq:
      forall m i r,
      run m i = r ->
      Run (Call m i) r.
    Proof.
      intros.
      assert (Run (Call m i) (run m i)). {
        apply run_call.
      }
      rewrite H in *.
      assumption.
    Qed.

    Lemma run_par_l_accept:
      forall p q c r,
      Run p Accept ->
      Run q Loop ->
      Run (c (pleft true)) r ->
      Run (Par p q c) r.
    Proof.
      intros.
      apply run_par_l_seq with (r1:=Accept) (b:=true); auto.
      apply dec_accept.
    Qed.

    Lemma run_par_r_accept:
      forall p q c r,
      Run q Accept ->
      Run p Loop ->
      Run (c (pright true)) r ->
      Run (Par p q c) r.
    Proof.
      intros.
      apply run_par_r_seq with (r1:=Accept) (b:=true); auto.
      apply dec_accept.
    Qed.

    Lemma run_par_l_reject:
      forall p q c r,
      Run p Reject ->
      Run q Loop ->
      Run (c (pleft false)) r ->
      Run (Par p q c) r.
    Proof.
      intros.
      apply run_par_l_seq with (r1:=Reject) (b:=false); auto.
      apply dec_reject.
    Qed.

    Lemma run_par_r_reject:
      forall p q c r,
      Run p Loop ->
      Run q Reject ->
      Run (c (pright false)) r ->
      Run (Par p q c) r.
    Proof.
      intros.
      apply run_par_r_seq with (r1:=Reject) (b:=false); auto.
      apply dec_reject.
    Qed.

    Lemma run_seq_reject:
      forall p q r,
      Run p Reject ->
      Run (q false) r ->
      Run (Seq p q) r.
    Proof.
      intros.
      apply run_seq_cont with (b:=false) (r1:=Reject).
      - assumption.
      - apply dec_reject.
      - assumption.
    Qed.

    Lemma run_seq_accept:
      forall p q r,
      Run p Accept ->
      Run (q true) r ->
      Run (Seq p q) r.
    Proof.
      intros.
      apply run_seq_cont with (b:=true) (r1:=Accept).
      - assumption.
      - apply dec_accept.
      - assumption.
    Qed.

    Lemma run_par_accept_accept:
      forall p q c r,
      Run p Accept ->
      Run q Accept ->
      Run (c (pboth true true)) r ->
      Run (Par p q c) r.
    Proof.
      intros.
      apply run_par_both with (r1:=Accept) (r2:=Accept) (b1:=true) (b2:=true);
      auto using dec_accept.
    Qed.

    Lemma run_par_accept_reject:
      forall p q c r,
      Run p Accept ->
      Run q Reject ->
      Run (c (pboth true false)) r ->
      Run (Par p q c) r.
    Proof.
      intros.
      apply run_par_both with (r1:=Accept) (r2:=Reject) (b1:=true) (b2:=false);
      auto using dec_reject, dec_accept.
    Qed.

    Lemma run_halt_with_to_dec:
      forall b r,
      Run (halt_with b) r ->
      Dec r b.
    Proof.
      intros.
      inversion H; subst; clear H.
      destruct b.
      - apply dec_accept.
      - apply dec_reject.
    Qed.

  End RUN.

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
    - intros N.
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
      | Run (Call _ _) _ => idtac
      | Run (Ret _) _ => idtac
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
      rewrite decode_encode_machine_input_rw in * ||
      rewrite decode_encode_pair_rw in * ||
      rewrite decode_encode_machine_rw in *).

  Ltac run_simpl_norm :=
    match goal with
    | [ H: ?x = ?x |- _] => clear H
    | [ H: Lang (Build _) _ |- _ ] => apply run_build in H
    | H: run (Build _) _ = _ |- _ => apply run_build in H
    | [ H: _ |- run (Build _) _ = _ ] => apply run_build
    | [ H: Run (halt_with _) _ |- _ ] => apply run_halt_with_to_dec in H
    | [ H: negb _ = true |- _ ] => apply negb_true_iff in H
    | [ H: negb _ = false |- _ ] => apply negb_false_iff in H
    | [ H: neg _ = Accept |- _ ] => apply neg_accept_rw in H
    | [ H: neg _ = Reject |- _ ] => apply neg_reject_rw in H
    | [ H: neg _ = Loop |- _ ] => apply neg_loop_rw in H
    | [ H: true = _ |- _ ] => symmetry in H
    | [ H: false = _ |- _ ] => symmetry in H
    | [ H: Reject = _ |- _ ] => symmetry in H
    | [ H: Loop = _ |- _ ] => symmetry in H
    | [ H: Accept = _ |- _ ] => symmetry in H
    end.

  Ltac run_simpl :=
    run_simpl_rw ||
    run_simpl_explode ||
    run_simpl_norm ||
    run_simpl_inv.


  (** Simplify everything *)

  Ltac run_simpl_all := repeat run_simpl.

End TuringBasics.
