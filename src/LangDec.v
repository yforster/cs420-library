Require Import Turing.
Require Import Coq.Bool.Bool.

Section Defs.

  (* -------------------------------------------------------------------------- *)

  Lemma decidable_to_compl:
    forall L,
    Decidable L ->
    Decidable (compl L).
  Proof.
    intros.
    destruct H as (m, H).
    apply decidable_def with (m:=mlet b <- m in halt_with (negb b)).
    apply decides_def.
    - unfold compl.
      split; intros. {
        intros N.
        assert (Run m i Accept) by eauto using decides_accept.
        inversion H0; subst; clear H0.
        run_simpl_all.
      }
      assert (Run m i Reject) by eauto using decides_reject.
      eapply run_seq_cont; eauto using dec_reject.
      constructor.
    - apply halts_to_decider.
      intros.
      destruct decides_to_run_dec with (p:=m) (L:=L) (i:=i) as (r, (b, (Hr, Hd))); auto.
      apply halts_seq with (b:=b) (r:=r); auto.
      apply halts_halt_with.
  Qed.

  Definition par_run (m1 m2:Prog) p :=
    forall i,
      (
        Run p i Accept /\ Run m1 i Accept
      ) \/ (
        Run p i Reject /\ (Run m1 i Reject \/ ~ Run m2 i Loop)
      ) \/ (
        Run p i Loop /\ Run m1 i Loop /\ Run m2 i Loop
      ).

  Definition par_mach M1 M2 : Prog :=
    Read (fun w =>
      plet b <- M1 \\ M2 in
      match b with
      | pleft true
      | pboth true _ => ACCEPT
      | pright false => ACCEPT
      | _ => REJECT
      end
    ).

  Lemma run_par_both_eq:
    forall i p1 p2 (k:par_result -> Prog) r1 r2 b1 b2 r,
    Run p1 i r1 ->
    Run p2 i r2 ->
    Dec r1 b1 ->
    Dec r2 b2 ->
    Run (k (pboth b1 b2)) i r ->
    Run (k (pleft b1)) i r ->
    Run (k (pright b2)) i r ->
    Run (Par p1 p2 k) i r.
  Proof.
    intros.
    apply run_par_both with (r1:=r1) (r2:=r2) (b1:=b1) (b2:=b2); auto.
    destruct (par_choice _ _ _ _) eqn:Hp; apply par_choice_spec in Hp;
    inversion Hp; subst; clear Hp; auto.
  Qed.

  Inductive DisjointResults: result -> result -> Prop :=
  | disjoint_accept_loop:
    DisjointResults Accept Loop
  | disjoint_accept_reject:
    DisjointResults Accept Reject
  | disjoint_loop_accept:
    DisjointResults Loop Accept
  | disjoint_reject_accept:
    DisjointResults Reject Accept.

  Lemma par_mach_lang:
    forall m1 m2,
    (forall i r1 r2, Run m1 i r1 -> Run m2 i r2 -> DisjointResults r1 r2) ->
    Recognizes (par_mach m1 m2) (fun i => Run m1 i Accept).
  Proof.
    unfold par_mach.
    intros m1 m2 Hr; intros.
    unfold Recognizes; intros.
    rewrite run_read_rw.
    split; intros.
    + (* Show that whenever the implementation accepts, then the language
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
        (* Notice that m1 accepted, thus i is in L *)
        assumption. (* Definition of Lang *) 
      * (* Case par_r_seq: m2 terminated *)
        (* If m2 terminates, then we have:
          Run (if b then REJECT else ACCEPT) Accept
          We perform a case analysis on b to figure out what was handled.
        *)
        destruct b; run_simpl_all.
        (* Our assumption Hr is saying that m1 and m2 cannot both reject.
           Thus, we use Hr to reach a contradiction. *)
        assert (Hd: DisjointResults Loop Reject) by eauto.
        inversion Hd.
      * (* Case par_r_both: both machines terminated at the same time *)
        (* since we have a match stuck on par_choice, we perform a case analysis
           on its output. *)
        destruct (par_choice _ _ _ _) eqn:Hp; 
        apply par_choice_spec in Hp; inversion Hp; subst; clear Hp;
        destruct b; run_simpl_all; try assumption.
        inversion H5; subst; clear H5.
        - (* m1 accepts and m2 rejects *)
          assumption.
        - (* m1 rejects and m2 rejects *)
          (* Absurd, because both machines cannot reject. *)
          assert (Hd: DisjointResults Reject Reject) by eauto.
          inversion Hd.
    + destruct (run_exists m2 i) as (r, He).
      destruct r.
      * (* Absurd case: both cannot accept *)
        run_simpl_all.
        assert (N: DisjointResults Accept Accept) by eauto.
        inversion N.
      * apply run_par_both_eq with (r1:=Accept) (r2:=Reject) (b1:=true) (b2:=false);
        auto using dec_accept, dec_reject, run_ret, run_call.
      * apply run_par_l_accept; auto using run_ret, run_call.
  Qed.

  Lemma par_run_spec:
    forall m1 m2,
    (forall i r1 r2, Run m1 i r1 -> Run m2 i r2 -> DisjointResults r1 r2) ->
    par_run m1 m2 (par_mach m1 m2).
  Proof.
    intros m1 m3 Hr.
    unfold par_run.
    unfold par_mach in *.
    intros.
    remember (Read _) as p.
    destruct (run_exists p i) as (r, He).
    destruct r.
    - left; split; auto.
      subst.
      inversion He; subst; clear He.
      inversion H0; subst; clear H0.
      + destruct b; run_simpl_all.
        assumption.
      + destruct b; run_simpl_all.
        assert (N: DisjointResults Loop Reject) by eauto.
        inversion N.
      + destruct (par_choice _ _ _ _) eqn:Hp;
        apply par_choice_spec in Hp;
        inversion Hp; subst; clear Hp;
        destruct b; run_simpl_all; auto.
        inversion H5; subst; clear H5; auto.
        assert (N: DisjointResults Reject Reject) by eauto.
        inversion N.
    - right.
      left. split; auto.
      subst.
      inversion He; subst; clear He.
      inversion H0; subst; clear H0;
      try (destruct b; run_simpl_all; auto).
      + right.
        intros N.
        assert (X: Accept = Loop) by (run_simpl; auto).
        inversion X.
      + destruct (par_choice _ _ _ _) eqn:Hp;
        apply par_choice_spec in Hp;
        inversion Hp; subst; clear Hp;
        destruct b; run_simpl_all; auto.
        inversion H5; subst; clear H5; auto. (* Dec r1 b1 *)
        assert (N: DisjointResults Accept Accept) by eauto.
        inversion N.
    - right.
      right.
      split; auto.
      subst.
      inversion He; subst; clear He.
      inversion H0; subst; clear H0;
      try (destruct b; run_simpl_all; auto).
      + destruct (par_choice _ _ _ _) eqn:Hp;
        apply par_choice_spec in Hp;
        inversion Hp; subst; clear Hp;
        destruct b; run_simpl_all; auto.
      + run_simpl_all.
        assert (N: DisjointResults Loop Loop) by eauto.
        inversion N.
  Qed.

  Lemma par_run_exists:
    forall m1 m2,
    (forall i r1 r2, Run m1 i r1 -> Run m2 i r2 -> DisjointResults r1 r2) ->
    exists p,
      Recognizes p (fun i => Run m1 i Accept) /\ par_run m1 m2 p.
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
    Run m1 i Reject ->
    Run m2 i Accept.
  Proof.
    intros.
    apply recognizes_run_reject with (L:=L) in H1; auto.
    apply co_recognizes_accept with (L:=L); auto.
  Qed.

  Lemma recognizes_co_recognizes_disjoint:
    forall m1 m2 L,
    Recognizes m1 L ->
    Recognizes m2 (compl L) ->
    (forall i r1 r2, Run m1 i r1 -> Run m2 i r2 -> DisjointResults r1 r2).
  Proof.
    intros.
    destruct r1.
    - apply H in H1.
      eapply co_recognizes_not_accept with (m:=m2) in H1; eauto.
      destruct r2; try contradiction; constructor.
    - apply recognizes_run_reject with (L:=L) in H1; auto.
      apply co_recognizes_accept with (m:=m2) in H1; auto.
      run_simpl.
      constructor.
    - apply recognizes_run_loop with (L:=L) in H1; auto.
      apply co_recognizes_accept with (m:=m2) in H1; auto.
      run_simpl.
      constructor.
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
      run_simpl_all.
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
      destruct (Hp i); intuition.
      apply recognizes_run_loop with (L:=L) in H2; auto.
      apply co_recognizes_accept with (m:=m2) in H2; auto.
      (* We have that m2 accepts i and also loops with i *)
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

