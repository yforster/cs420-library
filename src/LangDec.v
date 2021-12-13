Require Import Turing.
Require Import Coq.Bool.Bool.

Section Defs.
  Definition A_tm : lang := fun p =>
    let (M, w) := decode_machine_input p in
    Exec M w Accept.

  (** If [d] recognizes A_tm and machine d runs <M,w> *)
  Local Lemma a_tm_run_reject:
    forall d,
    Recognizes d A_tm ->
    forall w M,
    Exec d (encode_machine_input M w) Reject -> 
    forall r,
    Exec M w r ->
    r <> Accept.
  Proof.
    intros.
    intros N.
    apply recognizes_run_reject with (L:=A_tm) in H0; auto.
    unfold A_tm in H0.
    rewrite decode_encode_machine_input_rw in *.
    subst.
    contradiction.
  Qed.

  Local Lemma a_tm_run_loop:
    forall d,
    Recognizes d A_tm ->
    forall w m,
    Exec d (encode_machine_input m w) Loop -> 
    forall r,
    Exec m w r ->
    r <> Accept.
  Proof.
    intros.
    intros N; subst.
    apply recognizes_run_loop with (L:=A_tm) in H0; auto.
    unfold A_tm in H0.
    rewrite decode_encode_machine_input_rw in *.
    contradiction.
  Qed.

  Local Lemma a_tm_run_accept:
    forall d,
    Recognizes d A_tm ->
    forall w m,
    Exec d (encode_machine_input m w) Accept -> 
    Exec m w Accept.
  Proof.
    intros.
    apply recognizes_run_accept with (L:=A_tm) in H0; auto.
    unfold A_tm in *.
    rewrite decode_encode_machine_input_rw in *.
    assumption.
  Qed.

  (* -------------------------------------------------------------------------- *)

  Definition Negator (D:machine) :=
    fun p =>
      let M := decode_machine p in
      Exec D (encode_machine_input M p) Reject.

  (** [D] recognizes [A_tm].
      N accepts <M>, which means that D rejects <M, <M>>.
      Thus, M with <M> either loops or rejects, as recognizing
      A_tm is weaker then returning the same result.
    *)

  Lemma decider_not_reject:
    forall m i,
    Decider m ->
    ~ Exec m i Reject ->
    Exec m i Accept.
  Proof.
    intros.
    edestruct decider_to_run; eauto.
    intuition.
  Qed.

  Lemma decider_not_accept:
    forall m i,
    Decider m ->
    ~ Exec m i Accept ->
    Exec m i Reject.
  Proof.
    intros.
    edestruct decider_to_run; eauto.
    intuition.
  Qed.

  Lemma run_negator_accept:
    forall N D w,
    Recognizes D A_tm ->
    Recognizes N (Negator D) ->
    Exec N w Accept ->
    forall r,
    Exec (decode_machine w) w r ->
    r <> Accept.
  Proof.
    intros.
    apply recognizes_run_accept with (L:=Negator D) in H1; auto.
    eapply a_tm_run_reject in H2; eauto.
  Qed.

  Lemma negator_no:
    forall D w,
    Decider D ->
    ~ Negator D w ->
    Exec D <[ decode_machine w, w ]> Accept.
  Proof.
    intros.
    unfold Negator in H0.
    remember (encode_machine_input (decode_machine w) w) as j.
    (* If D does not reject, it must accept *)
    assert (Hd: Exec D j Accept) by eauto using decider_not_reject.
    subst.
    assumption.
  Qed.

  Lemma run_negator_reject:
    forall N D w,
    Recognizes D A_tm ->
    Recognizes N (Negator D) ->
    Exec N w Reject ->
    Decider D ->
    Exec (decode_machine w) w Accept.
  Proof.
    intros.
    apply recognizes_run_reject with (L:=Negator D) in H1; auto.
    assert (Ha: Exec D <[ decode_machine w, w ]> Accept) by auto using negator_no.
    apply a_tm_run_accept in Ha; auto.
  Qed.

  Lemma run_negator_loop:
    forall N D w,
    Recognizes D A_tm ->
    Recognizes N (Negator D) ->
    Exec N w Loop ->
    Decider D ->
    Exec (decode_machine w) w Accept.
  Proof.
    intros.
    apply recognizes_run_loop with (L:=Negator D) in H1; auto.
    apply negator_no in H1; auto.
    apply a_tm_run_accept in H1; auto.
  Qed.

  (**
    This new TM calls D to determine what M does when the input to M is its own
    description <M, <M>>. Once D has determined this information, it does the
    opposite. That is, it rejects if M accepts and accepts if M does not accept.

    The following is a description of [negator].
      negator = “On input <M>, where M is a TM :
          1. Run D on input <M, <M>>.
          2. Output the opposite of what D outputs. That is, if D accepts,
            reject ; and if D rejects, accept.”
  *)
  Definition negator D w :=
    let M := decode_machine w in
    (* D decides A_TM, thus we are running M with <M> *)
    mlet b <- Call D <[ M , w ]> in
    halt_with (negb b).

  Local Lemma negator_recognizes:
    forall H,
    Recognizes (Build (negator H)) (Negator H).
  Proof.
    intros.
    unfold Recognizes.
    split; intros. {
      unfold negator, Negator in *.
      run_simpl_all.
      inversion H0; subst; clear H0.
      run_simpl_all.
      assumption.
    }
    unfold Negator in *.
    run_simpl_all.
    unfold negator.
    apply run_seq_reject.
    - apply run_call.
      assumption.
    - apply run_ret.
  Qed.

  Lemma no_decides_a_tm:
    ~ exists m, Decides m A_tm.
  Proof.
    unfold not.
    (* We assume that A_TM is decidable and obtain a contradiction. *)
    intros N.
    (* Suppose that D is a decider for A_TM. *)
    destruct N as (D, is_dec).
    (* Now we construct a new Turing machine [negator] with D as a subroutine. *)
    assert (X:= negator_recognizes D).
    remember (Build (negator D)) as N.
    destruct is_dec as (Hrec, Hdec).
    (* What happens when we run [negator] with its own description <negator> as
      input? *)
    destruct (exec_exists N (encode_machine N)) as (r, He).
    assert (Hx := He).
    (* (Let us duplicate Heqr as we will need it later.) *)
    destruct r; subst.
    - eapply run_negator_accept with (D:=D) in He; eauto.
      rewrite decode_encode_machine_rw in *; auto.
    - apply run_negator_reject with (D:=D) in He; eauto.
      rewrite decode_encode_machine_rw in *.
      assert (N: Reject = Accept) by eauto using exec_fun.
      inversion N.
    - apply run_negator_loop with (D:=D) in He; eauto.
      rewrite decode_encode_machine_rw in *.
      assert (N: Loop = Accept) by eauto using exec_fun.
      inversion N.
  Qed.

  (** Theorem 4.11, pp 207 *)

  Theorem a_tm_undecidable:
    ~ Decidable A_tm.
  Proof.
    intros N.
    destruct N as (m, N).
    assert (Hx: exists m, Decides m A_tm). {
      exists m.
      assumption.
    }
    apply no_decides_a_tm in Hx.
    assumption.
  Qed.

  (* -------------------------------------------------------------------------- *)

  Local Definition A_tm_mach : machine :=
    Build (fun p => 
      let (M, w) := decode_machine_input p in
      Call M w).

  Lemma accept_to_a_tm:
    forall M L w,
    Recognizes M L ->
    L w ->
    A_tm <[ M, w ]>.
  Proof.
    intros.
    unfold A_tm.
    destruct (decode_machine_input _) as (M', w') eqn:Hr.
    run_simpl.
    inversion Hr; subst; clear Hr.
    apply recognizes_accept with (L:=L); auto.
  Qed.

  Lemma a_tm_to_accept:
    forall M L w,
    Recognizes M L ->
    A_tm <[ M, w ]> ->
    L w.
  Proof.
    intros.
    unfold A_tm in *.
    destruct (decode_machine_input _) as (M', w') eqn:Hr.
    run_simpl.
    inversion Hr; subst; clear Hr.
    apply recognizes_run_accept with (m:=M'); auto.
  Qed.

  Lemma a_tm_accept_iff:
    forall M L w,
    Recognizes M L ->
    A_tm <[ M, w ]> <-> L w.
  Proof.
    intros.
    split.
    - apply a_tm_to_accept; auto.
    - apply accept_to_a_tm; auto.
  Qed.

  Local Lemma a_tm_recognizes:
    Recognizes A_tm_mach A_tm.
  Proof.
    intros.
    unfold Recognizes.
    unfold A_tm_mach, A_tm.
    split; intros. {
      run_simpl_all.
      destruct (decode_machine_input i) as (m, w).
      run_simpl.
      assumption.
    }
    run_simpl.
    destruct (decode_machine_input i) as (m, w).
    apply run_call.
    assumption.
  Qed.

  Lemma a_tm_recognizable: Recognizable A_tm.
  Proof.
    apply recognizable_def with (m:=A_tm_mach).
    apply a_tm_recognizes.
  Qed.

  (* -------------------------------------------------------------------------- *)

  Definition Inv (m:machine) := fun i => Exec m i Reject.

  Definition InvM (n m:machine) := forall i r1 r2,
    Exec m i r1 ->
    Exec n i r2 ->
    neg r1 = r2.

  Lemma neg_dec:
    forall r1 r2 b,
    Dec r1 b ->
    Dec r2 (negb b) ->
    neg r1 = r2.
  Proof.
    intros.
    destruct r1, r2, b; simpl in *; inversion H; inversion H0; auto.
  Qed.

  Lemma inv_exists:
    forall m L,
    Recognizes m L ->
    exists n,
    Recognizes n (Inv m) /\ InvM n m.
  Proof.
    intros.
    exists (Build (fun w => (Seq (Call m w) (fun b => halt_with (negb b) )))).
    split. {
      unfold Recognizes.
      split; intros; unfold Inv in *; run_simpl_all.
      - inversion H0; subst; clear H0.
        run_simpl_all.
        assumption.
      - apply run_seq_reject.
        + apply run_call.
          assumption.
        + apply run_ret.
    }
    unfold InvM.
    intros.
    run_simpl.
    inversion H1; subst; clear H1;
    run_simpl_all.
    - eauto using neg_dec.
    - reflexivity.
  Qed.

  Local Lemma inv_compl_equiv:
    forall m L,
    Decides m L ->
    Equiv (Inv m) (compl L).
  Proof.
    unfold Equiv.
    intros.
    split; intros; unfold Inv, compl in *; simpl in *;
    eauto using decides_run_reject, decides_reject.
  Qed.

  Local Lemma recognizes_inv_compl:
    forall m n L,
    Decides m L ->
    Recognizes n (Inv m) ->
    Recognizes n (compl L).
  Proof.
    intros.
    assert (Hx : Equiv (Inv m) (compl L)). {
      apply inv_compl_equiv.
      auto.
    }
    apply lang_equiv with (m:=n) in Hx.
    apply Hx in H0.
    assumption.
  Qed.

  Lemma decides_to_compl:
    forall m L N,
    Decides m L ->
    Recognizes N (Inv m) ->
    InvM N m ->
    Decidable (compl L).
  Proof.
    intros.
    apply decidable_def with (m:=N).
    apply recognizes_inv_compl with (L:=L) in H0; auto.
    apply decides_def.
    * assumption.
    * unfold Decider; intros.
      intros Hn; subst.
      destruct (exec_exists m i) as (r, He).
      unfold InvM in *.
      assert (r = Loop). {
        assert (Hx: neg r = Loop) by eauto.
        destruct r; simpl in *; inversion Hx.
        reflexivity.
      }
      subst.
      apply decides_no_loop with (L:=L) in He; auto.
  Qed.

  Lemma decidable_to_compl:
    forall L,
    Decidable L ->
    Decidable (compl L).
  Proof.
    intros.
    destruct H as (m, H).
    destruct (inv_exists m L) as (N, (?, HN)); auto.
    + destruct H; auto.
    + apply decides_to_compl with (m:=m) (N:=N); auto.
  Qed.

  Definition par_run (m1 m2 m3:machine) :=
    forall i,
      (
        Exec m3 i Accept /\ Exec m1 i Accept
      ) \/ (
        Exec m3 i Reject /\ (Exec m1 i Reject \/ ~ Exec m2 i Loop)
      ) \/ (
        Exec m3 i Loop /\ Exec m1 i Loop /\ Exec m2 i Loop
      ).

  Definition par_mach M1 M2 (w: input) : Prog :=
      plet b <- Call M1 w \\ Call M2 w in
      match b with
      | pleft true
      | pboth true _ => ACCEPT
      | pright false => ACCEPT
      | _ => REJECT
      end
  .
(*
  Lemma lang_accept_rev:
    forall m w,
    Exec m w Accept ->
    Lang m w.
  Proof.
    intros.
    unfold Lang.
    symmetry.
    assumption.
  Qed.
*)
  Lemma run_par_both_eq:
    forall p1 p2 (k:par_result -> Prog) r1 r2 b1 b2 r,
    Run p1 r1 ->
    Run p2 r2 ->
    Dec r1 b1 ->
    Dec r2 b2 ->
    Run (k (pboth b1 b2)) r ->
    Run (k (pleft b1)) r ->
    Run (k (pright b2)) r ->
    Run (Par p1 p2 k) r.
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
    (forall i r1 r2, Exec m1 i r1 -> Exec m2 i r2 -> DisjointResults r1 r2) ->
    PRecognizes (par_mach m1 m2) (Lang m1).
  Proof.
    unfold par_mach.
    intros m1 m2 Hr; intros.
    apply p_recognizes_def.
    + intros.
      (* Show that whenever the implementation accepts, then the language
         accepts. We do this by thinking about the execution top to bottom:
         how did reached Accept?
         *)
      (* We perform an inversion on assumption H, which will return a case per
         constructor for par, since the first instructio nis a parallel call. *)
      inversion H; subst; clear H; run_simpl_all; auto.
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
    + intros.
      destruct (exec_exists m2 i) as (r, He).
      apply run_call in H.
      apply run_call in He.
      destruct r.
      * (* Absurd case: both cannot accept *)
        run_simpl_all.
        assert (N: DisjointResults Accept Accept) by eauto.
        inversion N.
      * apply run_par_both_eq with (r1:=Accept) (r2:=Reject) (b1:=true) (b2:=false);
        auto using dec_accept, dec_reject, run_ret.
      * apply run_par_l_accept; auto using run_ret.
  Qed.

  Lemma par_run_spec:
    forall m1 m2,
    (forall i r1 r2, Exec m1 i r1 -> Exec m2 i r2 -> DisjointResults r1 r2) ->
    par_run m1 m2 (Build (par_mach m1 m2)).
  Proof.
    intros m1 m3 Hr.
    unfold par_run.
    unfold par_mach in *.
    intros.
    remember (Build _) as m.
    destruct (exec_exists m i) as (r, He).
    destruct r.
    - left; split; auto.
      subst.
      run_simpl.
      inversion He; subst; clear He.
      + destruct b; run_simpl_all.
        assumption.
      + destruct b; run_simpl_all.
        assert (N: DisjointResults Loop Reject) by eauto.
        inversion N.
      + destruct (par_choice _ _ _ _) eqn:Hp;
        apply par_choice_spec in Hp;
        inversion Hp; subst; clear Hp;
        destruct b; run_simpl_all; auto.
        inversion H4; subst; clear H4; auto.
        assert (N: DisjointResults Reject Reject) by eauto.
        inversion N.
    - right.
      left. split; auto.
      subst; run_simpl.
      inversion He; subst; clear He;
      try (destruct b; run_simpl_all; auto).
      + right.
        intros N.
        assert (X: Accept = Loop) by (run_simpl; auto).
        inversion X.
      + destruct (par_choice _ _ _ _) eqn:Hp;
        apply par_choice_spec in Hp;
        inversion Hp; subst; clear Hp;
        destruct b; run_simpl_all; auto.
        inversion H4; subst; clear H4; auto.
        assert (N: DisjointResults Accept Accept) by eauto.
        inversion N.
    - right.
      right.
      split; auto.
      subst; run_simpl.
      inversion He; subst; clear He;
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
    (forall i r1 r2, Exec m1 i r1 -> Exec m2 i r2 -> DisjointResults r1 r2) ->
    exists m3,
      Recognizes m3 (Lang m1) /\ par_run m1 m2 m3.
  Proof.
    intros.
    exists (Build (par_mach m1 m2)).
    split.
    - rewrite <- p_recognizes_rw.
      auto using par_mach_lang.
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

  Local Lemma reject_recognize_to_accept_co_recognize:
    forall m1 m2 L,
    Recognizes m1 L ->
    Recognizes m2 (compl L) ->
    forall i,
    Exec m1 i Reject ->
    Exec m2 i Accept.
  Proof.
    intros.
    apply recognizes_run_reject with (L:=L) in H1; auto.
    apply co_recognizes_accept with (L:=L); auto.
  Qed.

  Lemma recognizes_co_recognizes_disjoint:
    forall m1 m2 L,
    Recognizes m1 L ->
    Recognizes m2 (compl L) ->
    (forall i r1 r2, Exec m1 i r1 -> Exec m2 i r2 -> DisjointResults r1 r2).
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
    destruct par_run_exists with (m1:=m1) (m2:=m2) as (mpar, (Hr,Hp));
    eauto using recognizes_co_recognizes_disjoint.
    apply decidable_def with (m:=mpar).
    apply decides_def.
    + unfold Recognizes.
      intros.
      rewrite (Hr i).
      rewrite (H i).
      intuition.
    + unfold Decider.
      intros.
      assert (Hp := Hp i).
      destruct (exec_exists m1 i) as (r', He).
      intros N; subst.
      destruct r'.
      - unfold Lang in *.
        assert (Hr := Hr i).
        rewrite <- Hr in He.
        assert (N: Loop = Accept) by (run_simpl; auto).
        inversion N.
      - apply reject_recognize_to_accept_co_recognize with (m2:=m2) (L:=L) in He; auto.
        intuition; run_simpl_all.
      - (* Since [m1 i] loops, then [m2 i] accepts : *)
        apply recognizes_run_loop with (L:=L) in He; auto.
        apply co_recognizes_accept with (m:=m2) in He; auto.
        (* Let us simplify [m2] accepts in [Hp] *)
        intuition; run_simpl_all.
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

  (* -------------------------------------------------------------------------- *)

  (** Corollary 4.23 *)

  Theorem co_a_tm_not_recognizable:
    ~ Recognizable (compl A_tm).
  Proof.
    intros N.
    assert (Hx : Recognizable A_tm /\ Recognizable (compl A_tm)). {
      split.
      - apply a_tm_recognizable.
      - assumption.
    }
    apply dec_rec_co_rec in Hx.
    apply a_tm_undecidable.
    assumption.
  Qed.
  End Defs.

