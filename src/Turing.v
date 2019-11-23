Require Import Coq.Setoids.Setoid.
Require Import Coq.Bool.Bool.

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

  Inductive par_result :=
  | pleft: bool -> par_result
  | pright: bool -> par_result
  | pboth: bool -> bool -> par_result.

  Inductive Prog :=
  | Seq: Prog -> (bool -> Prog) -> Prog
  | Call: machine -> input -> Prog
  | Ret: result -> Prog
  | Par: Prog -> Prog -> (par_result -> Prog) -> Prog.

  Inductive Dec : result -> bool -> Prop :=
  | dec_accept:
    Dec Accept true
  | dec_reject:
    Dec Reject false.

  Inductive Run: Prog -> result -> Prop :=
  | run_ret:
    forall r,
    Run (Ret r) r
  | run_call:
    forall m i,
    Run (Call m i) (run m i)
  | run_seq_cont:
    forall p q b r1 r2,
    Run p r1 ->
    Dec r1 b ->
    Run (q b) r2 ->
    Run (Seq p q) r2
  | run_seq_loop:
    forall p q,
    Run p Loop ->
    Run (Seq p q) Loop
  | run_par_l_seq:
    forall p q c r1 r2 b,
    Run p r1 ->
    Run q Loop ->
    Dec r1 b ->
    Run (c (pleft b)) r2 ->
    Run (Par p q c) r2
  | run_par_r_seq:
    forall p q c r1 r2 b,
    Run p Loop ->
    Run q r1 ->
    Dec r1 b ->
    Run (c (pright b)) r2 ->
    Run (Par p q c) r2
  | run_par_both:
    forall p q c r1 r2 r3 b1 b2,
    Run p r1 ->
    Run q r2 ->
    Dec r1 b1 ->
    Dec r2 b2 ->
    Run (c (pboth b1 b2)) r3 ->
    Run (Par p q c) r3
  | run_par_loop:
    forall p q c,
    Run p Loop ->
    Run q Loop ->
    Run (Par p q c) Loop.

  Notation "'mlet' x <- e 'in' c" := (Seq e (fun x => c)) (at level 60, right associativity).
  Notation "'plet' x <- e1 '\\' e2 'in' c" := (Par e1 e2 (fun (x:par_result) => c)) (at level 60, right associativity).

  Notation ACCEPT := (Ret Accept).
  Notation REJECT := (Ret Reject).
  Notation LOOP := (Ret Loop).
  Parameter Build : (input -> Prog) -> machine.
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

  (** We use a direct definition of recognition. *)

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

  (** A language is recognizable, that is
      there is some machine m that recognizes it. *)

  Definition Recognizable (L:lang) : Prop := exists m, Recognizes m L.

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
      | Run (Seq _ _) Loop => idtac
      | Run (Seq _ _) Accept => idtac
      | Run (Seq _ _) Reject => idtac
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
        | _ => fail
        end; inversion H
    end.

  Ltac run_simpl_norm :=
    match goal with
    | [ H: ?x = ?x |- _] => clear H
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

  Ltac run_simpl := ( run_simpl_explode || run_simpl_norm || run_simpl_inv ).


  (** Simplify everything *)

  Ltac run_simpl_all := repeat run_simpl.

End TuringBasics.
