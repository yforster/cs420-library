Require Import Turing.

Module Decidability (Tur: Turing).
  Import Tur.
  Module B := TuringBasics Tur.
  Import B.

  Section Defs.
  Definition A_tm : lang := fun p =>
    let (M, w) := decode_machine_input p in
    run M w = Accept.

  (** If [d] recognizes A_tm and machine d runs <M,w> *)
  Local Lemma a_tm_run_reject:
    forall d,
    Recognizes d A_tm ->
    forall w M,
    run d (encode_machine_input M w) = Reject -> 
    run M w <> Accept.
  Proof.
    intros.
    intros N.
    apply recognizes_run_reject with (L:=A_tm) in H0; auto.
    unfold A_tm in H0.
    rewrite decode_encode_machine_input_rw in *.
    contradiction.
  Qed.

  Local Lemma a_tm_run_loop:
    forall d,
    Recognizes d A_tm ->
    forall w m,
    run d (encode_machine_input m w) = Loop -> 
    run m w <> Accept.
  Proof.
    intros.
    intros N.
    apply recognizes_run_loop with (L:=A_tm) in H0; auto.
    unfold A_tm in H0.
    rewrite decode_encode_machine_input_rw in *.
    contradiction.
  Qed.

  Local Lemma a_tm_run_accept:
    forall d,
    Recognizes d A_tm ->
    forall w m,
    run d (encode_machine_input m w) = Accept -> 
    run m w = Accept.
  Proof.
    intros.
    apply recognizes_run_accept with (L:=A_tm) in H0; auto.
    unfold A_tm in *.
    rewrite decode_encode_machine_input_rw in *.
    assumption.
  Qed.

  (* -------------------------------------------------------------------------- *)

  Local Definition Negator (D:machine) :=
    fun p =>
      let M := decode_machine p in
      neg (run D (encode_machine_input M p)) = Accept.

  (** [D] recognizes [A_tm].
      N accepts <M>, which means that D rejects <M, <M>>.
      Thus, M with <M> either loops or rejects, as recognizing
      A_tm is weaker then returning the same result.
    *)

  Local Lemma run_negator_accept:
    forall N D w,
    Recognizes D A_tm ->
    Recognizes N (Negator D) ->
    run N w = Accept ->
    run (decode_machine w) w <> Accept.
  Proof.
    intros.
    apply recognizes_run_accept with (L:=Negator D) in H1; auto.
    unfold Negator in *.
    rewrite neg_accept_rw in *.
    apply a_tm_run_reject in H1; auto.
  Qed.

  Local Lemma run_negator_reject:
    forall N D w,
    Recognizes D A_tm ->
    Recognizes N (Negator D) ->
    run N w = Reject ->
    Decider D ->
    run (decode_machine w) w = Accept.
  Proof.
    intros.
    apply recognizes_run_reject with (L:=Negator D) in H1; auto.
    unfold Negator in H1.
    rewrite neg_accept_rw in *.
    remember (encode_machine_input (decode_machine w) w) as j.
    apply decider_not_reject_to_accept in H1; auto.
    subst.
    apply a_tm_run_accept in H1; auto.
  Qed.

  Local Lemma run_negator_loop:
    forall N D w,
    Recognizes D A_tm ->
    Recognizes N (Negator D) ->
    run N w = Loop ->
    Decider D ->
    run (decode_machine w) w = Accept.
  Proof.
    intros.
    apply recognizes_run_loop with (L:=Negator D) in H1; auto.
    unfold Negator in H1.
    rewrite neg_accept_rw in *.
    apply decider_not_reject_to_accept in H1; auto.
    apply a_tm_run_accept in H1; auto.
  Qed.

  Local Definition halt_with (b:bool) := Ret (if b then Accept else Reject).

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
  Local Definition negator D w :=
    let M := decode_machine w in
    (* D decides A_TM, thus we are running M with <M> *)
    mlet b <- Call D << M, w>> in
    halt_with (negb b).

  Local Lemma negator_recognizes:
    forall H,
    Recognizes (Build (negator H)) (Negator H).
  Proof.
    intros.
    unfold Recognizes.
    split; intros. {
      apply run_build in H0.
      unfold negator, Negator in *.
      run_simpl_all.
      inversion H4; subst; clear H4; simpl in *.
      - inversion H6.
      - reflexivity.
    }
    unfold Negator in *.
    apply run_build.
    unfold negator.
    rewrite neg_accept_rw in *.
    apply run_seq_reject.
    - apply run_call_eq.
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
    remember (run N (encode_machine N)) as r.
    symmetry in Heqr.
    (* (Let us duplicate Heqr as we will need it later.) *)
    assert (Hx := Heqr).
    destruct r.
    - subst.
      apply run_negator_accept with (D:=D) in Heqr; auto.
      rewrite decode_encode_machine_rw in *.
      contradiction.
    - apply run_negator_reject with (D:=D) in Heqr; eauto.
      rewrite decode_encode_machine_rw in *.
      rewrite Hx in *.
      inversion Heqr.
    - apply run_negator_loop with (D:=D) in Heqr; eauto.
      rewrite decode_encode_machine_rw in *.
      rewrite Hx in *.
      inversion Heqr.
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

  Local Lemma a_tm_recognizes:
    Recognizes A_tm_mach A_tm.
  Proof.
    intros.
    unfold Recognizes.
    unfold A_tm_mach, A_tm.
    split; intros. {
      apply run_build in H.
      destruct (decode_machine_input i) as (m, w).
      run_simpl.
      reflexivity.
    }
    apply run_build.
    destruct (decode_machine_input i) as (m, w).
    apply run_call_eq.
    assumption.
  Qed.

  Lemma a_tm_recognizable: Recognizable A_tm.
  Proof.
    apply recognizable_def with (m:=A_tm_mach).
    apply a_tm_recognizes.
  Qed.

  (* -------------------------------------------------------------------------- *)

  Local Definition Inv (m:machine) := fun i => neg (run m i) = Accept.

  Local Definition InvM (n m:machine) := forall i, neg (run m i) = run n i.

  Local Lemma inv_exists:
    forall m L,
    Recognizes m L ->
    exists n,
    Recognizes n (Inv m) /\ InvM n m.
  Proof.
    intros.
    exists (Build (fun w => (Seq (Call m w) (fun b => halt_with (negb b) )))).
    split. {
      unfold Recognizes.
      split; intros.
      - unfold Inv.
        apply run_build in H0.
        run_simpl_all.
        inversion H4; subst; clear H4;
        inversion H6; subst; clear H6.
        reflexivity.
      - apply run_build.
        unfold Inv in *.
        rewrite neg_accept_rw in *.
        apply run_seq_reject.
        + apply run_call_eq.
          assumption.
        + apply run_ret.
    }
    unfold InvM.
    intros.
    remember (run (Build _) i) as r.
    symmetry in Heqr.
    apply run_build in Heqr.
    inversion Heqr; subst; clear Heqr;
    run_simpl_all.
    - compute in H5.
      inversion H3; subst; clear H3.
      + run_simpl.
        reflexivity.
      + run_simpl.
        reflexivity.
    - rewrite H4.
      reflexivity.
  Qed.

  Local Lemma inv_compl_equiv:
    forall m L,
    Decides m L ->
    Equiv (Inv m) (compl L).
  Proof.
    unfold Equiv.
    intros.
    split; intros; unfold Inv, compl in *; simpl in *.
    - rewrite neg_accept_rw in *.
      apply decides_run_reject with (m:=m); auto.
    - apply decides_reject with (m:=m) in H0; auto.
      rewrite H0.
      reflexivity.
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

  Local Lemma decides_to_compl:
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
      intros Hn.
      rewrite <- H1 in Hn.
      rewrite neg_loop_rw in *.
      apply decides_no_loop with (L:=L) in Hn; auto.
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

  Local Definition par_run (m1 m2 m3:machine) :=
    forall i,
      match run m3 i with
      | Accept => run m1 i = Accept
      | Reject => run m1 i = Reject \/ run m2 i <> Loop 
      | Loop => run m1 i = Loop /\ run m2 i = Loop
      end.

  Local Definition par_mach M1 M2 : machine :=
    Build (fun w =>
      plet b <- Call M1 w \\ Call M2 w in
      match b with
      | pleft true
      | pboth true _ => ACCEPT
      | _ => REJECT
      end
    ).

  Local Lemma lang_accept_rev:
    forall m w,
    Accept = run m w ->
    Lang m w.
  Proof.
    intros.
    unfold Lang.
    symmetry.
    assumption.
  Qed.

  Local Lemma par_mach_lang:
    forall m1 m2,
    Recognizes (par_mach m1 m2) (Lang m1).
  Proof.
    unfold par_mach.
    unfold Recognizes.
    intros.
    rewrite <- run_build.
    split.
    + intros.
      inversion H; subst; clear H.
      * destruct b. {
          run_simpl_all.
          apply lang_accept_rev.
          assumption.
        }
        run_simpl_all.
      * run_simpl_all.
      * run_simpl_all.
        inversion H5; subst; clear H5. {
          run_simpl_all.
          apply lang_accept_rev.
          assumption.
        }
        run_simpl.
    + intros.
      remember (run m2 i) as r.
      symmetry in Heqr.
      destruct r.
      * apply run_par_accept_accept; auto using run_call_eq, run_ret.
      * apply run_par_accept_reject; auto using run_call_eq, run_ret.
      * apply run_par_l_accept; auto using run_call_eq, run_ret.
  Qed.

  Local Lemma par_run_spec:
    forall m1 m2,
    par_run m1 m2 (par_mach m1 m2).
  Proof.
    unfold par_run.
    unfold par_mach in *.
    intros.
    remember (run (Build _) i) as r.
    symmetry in Heqr.
    apply run_build in Heqr.
    inversion Heqr; subst; clear Heqr.
    - run_simpl_all.
      inversion H5; subst; clear H5;
      inversion H6; subst; clear H6;
      intuition.
    - run_simpl_all.
      right.
      intros N.
      rewrite N in *.
      rewrite H in *.
      inversion H5.
    - run_simpl_all.
      inversion H4; subst; clear H4;
      inversion H7; subst; clear H7; auto.
    - run_simpl_all.
      rewrite H.
      intuition.
  Qed.

  Local Lemma par_run_exists:
    forall m1 m2,
    exists m3,
      Recognizes m3 (Lang m1) /\ par_run m1 m2 m3.
  Proof.
    intros.
    exists (par_mach m1 m2).
    split.
    - apply par_mach_lang.
    - apply par_run_spec.
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
    run m1 i = Reject ->
    run m2 i = Accept.
  Proof.
    intros.
    apply recognizes_run_reject with (L:=L) in H1; auto.
    apply co_recognizes_accept with (L:=L); auto.
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
    destruct par_run_exists with (m1:=m1) (m2:=m2) as (mpar, (Hr,Hp)).
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
      remember (run m1 i).
      symmetry in Heqr.
      destruct r.
      - unfold Lang in *.
        intros N.
        assert (Hr := Hr i).
        rewrite <- Hr in Heqr.
        rewrite N in *.
        inversion Heqr.
      - apply reject_recognize_to_accept_co_recognize with (m2:=m2) (L:=L) in Heqr; auto.
        destruct (run mpar i).
        * inversion Hp.
        * intros N; inversion N.
        * destruct Hp as (N, _).
          inversion N.
      - apply recognizes_run_loop with (L:=L) in Heqr; auto.
        apply co_recognizes_accept with (m:=m2) in Heqr; auto.
        destruct (run mpar i).
        * inversion Hp.
        * intros N; inversion N.
        * destruct Hp as (_, Hp).
          rewrite Hp in *.
          inversion Heqr.
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
End Decidability.
