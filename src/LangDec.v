
Require Import Turing.
Require Import Coq.Bool.Bool.


  (** When running two programs in parallel, we get to know
    which of the two programs has terminated and how they
    terminated. *)
  Inductive par_result :=
  | pleft: bool -> par_result
  | pright: bool -> par_result
  | pboth: bool -> bool -> par_result.

  (**
    `Par p1 p2 f` interleaves the exection of program `p1`
    and `p2`. If either (or both) terminate, then
    call `f` with the termination result. 
   *)
  Parameter Par: Prog -> Prog -> (par_result -> Prog) -> Prog.

  (** We define a notion for parallel sequencing. *)
  Notation "'plet' x <- e1 '\\' e2 'in' c" := (Par e1 e2 (fun (x:par_result) => c)) (at level 60, right associativity).

  Inductive RunPar : Prog -> Prog -> (par_result -> Prog) -> input -> bool -> Prop :=
  | run_par_l:
    forall p q c r b i,
    Run p i b ->
    Loop q i ->
    Run (c (pleft b)) i r ->
    RunPar p q c i r
  | run_par_r:
    (** If `p` loops and `q` terminates, then
       we run continuation `c` with `cright b`. *)
    forall p q c r b i,
    Loop p i ->
    Run q i b ->
    Run (c (pright b)) i r ->
    RunPar p q c i r
  | run_par_both:
    (** If both `p` and `q` terminate, then
       we run continuation `c` with `pboth b1 b2`. *)
    forall p1 p2 c r b1 b2 i,
    Run p1 i b1 ->
    Run p2 i b2 ->
    Run (c (pboth b1 b2)) i r ->
    RunPar p1 p2 c i r
  .

  Axiom run_par_rw:
    forall p q c i b,
    Run (Par p q c) i b <-> RunPar p q c i b.


Section Defs.

  (* -------------------------------------------------------------------------- *)

  Lemma decidable_to_compl:
    forall L,
    Decidable L ->
    Decidable (compl L).
  Proof.
    intros.
    destruct H as (m, H).
    apply decidable_def with (m:=mlet b <- m in Ret (negb b)).
    apply decides_def.
    - unfold compl.
      split; intros. {
        intros N.
        assert (Run m i true) by eauto using decides_accept.
        inversion H0; subst; clear H0.
        run_simpl_all.
      }
      assert (Run m i false) by eauto using decides_reject.
      eapply run_seq; eauto.
      constructor.
    - apply decider_def.
      intros.
      assert (Ha: Halt m i) by eauto using decides_to_halt.
      rewrite halt_rw in Ha.
      destruct Ha as (b, Ha).
      econstructor; eauto.
      constructor.
  Qed.

  Definition par_run (m1 m2:Prog) p :=
    forall i,
      (
        Run p i true /\ Run m1 i true
      ) \/ (
        Run p i false /\ (Run m1 i false \/ Halt m2 i)
      ) \/ (
        Loop p i /\ Loop m1 i /\ Loop m2 i
      ).

  Definition par_mach M1 M2 : Prog :=
    Read (fun w =>
      plet b <- M1 \\ M2 in
      Ret (match b with
      | pleft true
      | pboth true _
      | pright false => true
      | _ => false
      end)
    ).

  Definition Disjoint p1 p2 i : Prop :=
    (Run p1 i true /\ Negative p2 i)
    \/
    (Negative p1 i /\ Run p2 i true).

  Lemma disjoint_run_true_1_rw:
    forall p1 p2 i,
    Disjoint p1 p2 i ->
    Negative p2 i <-> Run p1 i true.
  Proof.
    intros.
    split; intros. {
      destruct H as [(Ha,Hb)|(Ha,Hb)]. {
        assumption.
      }
      (* Contradiction: run p2 and neg p2 *)
      run_simpl_all.
    }
    destruct H; intuition.
    (* Contradiction: neg p1 and run p1 *)
    run_simpl_all.
  Qed.

  Lemma disjoint_run_true_2_rw:
    forall p1 p2 i,
    Disjoint p1 p2 i ->
    Negative p1 i <-> Run p2 i true.
  Proof.
    intros.
    split; intros. {
      destruct H; intuition.
      (* Contradiction: run p1 and neg p1 *)
      run_simpl_all.
    }
    destruct H as [(Ha,Hb)|(Ha,Hb)]; intuition.
    (* We have reached a contradiction. p2 true and p2 neg *) 
    run_simpl_all.
  Qed.

  Lemma par_mach_lang:
    forall m1 m2,
    (forall i, Disjoint m1 m2 i) ->
    Recognizes (par_mach m1 m2) (fun i => Run m1 i true).
  Proof.
    unfold par_mach.
    intros m1 m2 Hr; intros.
    unfold Recognizes; intros.
    rewrite run_read_rw.
    rewrite run_par_rw in *.
    split; intros. {
      (* Show that whenever the implementation accepts, then the language
         accepts. We do this by thinking about the execution top to bottom:
         how did reached Accept?
         *)
      (* We perform an inversion on assumption H, which will return a case per
         constructor for par, since the first instructio nis a parallel call. *)
      inversion H; subst; clear H; run_simpl_all.
      * (* Case par_l_seq: m1 terminated*)
        (* If m1 terminates, then we have:
          Run (if b then ACCEPT else REJECT) Accept
          We perform a case analysis on b to figure out what was handled.
        *)
        destruct b; run_simpl_all.
        assumption.
      * (* Case par_r_seq: m2 terminated *)
        (* If m2 terminates, then we have:
          Run (if b then REJECT else ACCEPT) Accept
          We perform a case analysis on b to figure out what was handled.
        *)
        destruct b; run_simpl_all.
        assert (Ha: Negative m1 i). { auto using negative_loop. }
        rewrite (disjoint_run_true_2_rw _ _ _ (Hr i)) in *.
        run_simpl_all.
      * (* Both machines terminated at the same time *)
        destruct b1; run_simpl_all.
        assumption.
    }
    destruct (halt_or_loop m2 i) as [He|Hl]. {
      assert (Run m2 i false). {
        rewrite halt_rw in *.
        destruct He as ([],He); auto.
        rewrite <- (disjoint_run_true_1_rw _ _ _ (Hr i)) in H.
        (* Contradiction: run m2 and neg m2 *)
        run_simpl_all.
      }
      eapply run_par_both; eauto.
      constructor.
    }
    apply run_par_l with (b:=true); auto.
    constructor.
  Qed.

  Lemma disjoint_halt_halt:
    forall p1 p2 i,
    Disjoint p1 p2 i ->
    Halt p1 i ->
    Halt p2 i ->
    exists b, Run p1 i b /\ Run p2 i (negb b).
  Proof.
    intros.
    rewrite halt_rw in *.
    destruct H0 as ([], Ha), H1 as ([], Hb); eauto.
    - erewrite <- disjoint_run_true_1_rw in Ha; eauto.
      run_simpl_all.
    - assert (Hr: Negative p2 i). { auto using negative_run_false. }
      erewrite disjoint_run_true_1_rw in Hr; eauto.
  Qed.

  Lemma par_run_spec:
    forall m1 m2,
    (forall i, Disjoint m1 m2 i) ->
    par_run m1 m2 (par_mach m1 m2).
  Proof.
    intros m1 m3 Hr.
    unfold par_run.
    unfold par_mach in *.
    intros.
    remember (Read _) as p.
    destruct (halt_or_loop p i) as [Ha|Hl]; subst. {
      rewrite halt_rw in *.
      destruct Ha as ([], Ha). {
        left; split; auto.
        inversion_clear Ha.
        rewrite run_par_rw in *.
        inversion_clear H.
        + destruct b; run_simpl_all.
          assumption.
        + destruct b; run_simpl_all.
          assert (Hrej: Negative m3 i). { auto using negative_run_false. }
          rewrite disjoint_run_true_1_rw in Hrej; eauto.
        + destruct b1; run_simpl_all.
          assumption.
      }
      right.
      left.
      split; auto.
      rewrite run_read_rw in *.
      rewrite run_par_rw in *.
      inversion_clear Ha.
      + destruct b; run_simpl_all.
        auto.
      + destruct b; run_simpl_all.
        right.
        eauto.
      + destruct b1; run_simpl_all; auto.
    }
    right.
    right.
    split; auto.
    assert (Hr := Hr i).
    rewrite loop_read_rw in *.
      split. {
        rewrite loop_rw in *.
        intros N.
        contradict Hl.
        destruct (halt_or_loop m3 i). {
          edestruct disjoint_halt_halt as (b, (Ha,Hb)); eauto.
          eapply run_to_halt; eauto.
          rewrite run_par_rw.
          eapply run_par_both; eauto.
          constructor.
        }
        assert (Run m1 i true). {
          destruct Hr as [(?,?)|(?,?)]; auto.
          run_simpl_all.
        }
        apply run_to_halt with (b:=true); auto.
        rewrite run_par_rw.
        eapply run_par_l; eauto.
        constructor.
      }
      rewrite loop_rw in *.
      intros N.
      contradict Hl.
      destruct (halt_or_loop m1 i). {
        edestruct disjoint_halt_halt as (b, (Ha,Hb)); eauto.
        eapply run_to_halt; eauto.
        rewrite run_par_rw.
        eapply run_par_both; eauto.
        constructor.
      }
      assert (Run m3 i true). {
        rewrite <- disjoint_run_true_2_rw; eauto.
        auto using negative_loop.
      }
      rewrite halt_rw in *.
      exists false.
      rewrite run_par_rw.
      eapply run_par_r; eauto.
      constructor.
  Qed.

  Lemma par_run_exists:
    forall m1 m2,
    (forall i, Disjoint m1 m2 i) ->
    exists p,
      Recognizes p (fun i => Run m1 i true) /\ par_run m1 m2 p.
  Proof.
    intros.
    exists (par_mach m1 m2).
    split.
    - auto using par_mach_lang.
    - auto using par_run_spec.
  Qed.

  Lemma decidable_to_co_recognizable:
    forall L,
    Decidable L ->
    Recognizable (compl L).
  Proof.
    intros.
    apply decidable_to_compl in H.
    apply decidable_to_recognizable.
    assumption.
  Qed.

  Lemma reject_recognize_to_accept_co_recognize:
    forall m1 m2 L,
    Recognizes m1 L ->
    Recognizes m2 (compl L) ->
    forall i,
    Run m1 i false ->
    Run m2 i true.
  Proof.
    intros.
    apply recognizes_run_reject with (L:=L) in H1; auto.
    apply co_recognizes_accept with (L:=L); auto.
  Qed.

  Lemma recognizes_co_recognizes_disjoint:
    forall m1 m2 L,
    Recognizes m1 L ->
    Recognizes m2 (compl L) ->
    (forall i, Disjoint m1 m2 i).
  Proof.
    intros.
    unfold Disjoint.
    destruct
      (run_true_or_negative m1 i) as [Ha|Ha],
      (run_true_or_negative m2 i) as [Hb|Hb];
      (* Two cases are trivial. *)
      auto.
    - (* We have L i *)
      assert (H_yes: L i) by (eapply recognizes_run_accept; eauto).
      (* But we also have ~ L i *)
      contradict H_yes.
      eapply recognizes_run_accept with (L:=compl L) in Hb; eauto.
    - assert (~ L i). {
        (* (m1, i) is negative, and m1 recognizes L, thus  ~ L i *) 
        eauto using recognizes_inv_negative.
      }
      (* Since we have ~ L i and m2 recognizes L, thus (m2, i) returns true *)
      assert (Run m2 i true). { eapply co_recognizes_accept; eauto. }
      (* But m2 i is negative *)
      run_simpl_all.
  Qed.

  Lemma recognizable_co_recognizable_to_decidable:
    forall L,
    Recognizable L ->
    Recognizable (compl L) ->
    Decidable L.
  Proof.
    intros.
    destruct H as (m1, H).
    destruct H0 as (m2, H0).
    destruct par_run_exists with (m1:=m1) (m2:=m2) as (mpar, (Hr,Hp)). {
      intros.
      eapply recognizes_co_recognizes_disjoint with (m1:=m1) (m2:=m2); eauto.
    }
    apply decidable_def with (m:=mpar).
    apply decides_def.
    + unfold Recognizes.
      intros.
      rewrite (Hr i).
      rewrite (H i).
      reflexivity.
    + unfold Decider.
      intros.
      assert (Hp := Hp i).
      intuition; eauto using run_to_halt.
      apply recognizes_run_loop with (L:=L) in H2; auto.
      apply co_recognizes_accept with (m:=m2) in H2; auto.
      (* m2 runs and loops, absurd *)
      run_simpl_all.
  Qed.

  (** Theorem 4.22 *)

  Theorem dec_rec_co_rec:
    forall L,
    Decidable L <-> (Recognizable L /\ Recognizable (compl L)).
  Proof.
    split; intros.
    - split.
      + apply decidable_to_recognizable.
        assumption.
      + apply decidable_to_co_recognizable.
        assumption.
    - destruct H.
      apply recognizable_co_recognizable_to_decidable; auto.
  Qed.

End Defs.

