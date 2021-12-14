Require Coq.Classes.RelationClasses.
Require Coq.Relations.Relations.
Require Coq.Classes.Morphisms.

Require Import Coq.Setoids.Setoid.

Require Import Turing.Turing.
Require Import Turing.LangDec.

  Section HALT_TM. (* ---------------------- Theorem 5.1 --------------------- *)

  Definition HALT_tm : lang := fun p =>
    let (M, w) := decode_prog_input p in
    ~ Run M w Loop.

  Definition HALT_tm_to_A_tm D : lang :=
    (fun p =>
      let (M, w) := decode_prog_input p in
      Run D p Accept /\ Run M w Accept
    ).

  Definition HALT_tm_impl D :=
    Read (fun p =>
      let (M, w) := decode_prog_input p in
      mlet b <- D in
      if b then With w M else REJECT 
    ).

  Lemma halt_tm_mach_spec:
    forall D,
    Recognizes (HALT_tm_impl D) (HALT_tm_to_A_tm D).
  Proof.
    unfold Recognizes, HALT_tm_impl, HALT_tm_to_A_tm.
    intros.
    rewrite run_read_rw.
    destruct (decode_prog_input i) as (M,w) eqn:Heq.
    split; intros.
    - inversion H; subst; clear H.
      destruct b; run_simpl_all.
      intuition.
    - intuition.
      apply run_seq_accept; auto.
      repeat (constructor; auto).
  Qed.

  Lemma halt_mach_loop:
    forall D p,
    Run (HALT_tm_impl D) p Loop ->
    let (M, w) := decode_prog_input p in
    (Run D p Accept /\ Run M w Loop) \/ Run D p Loop.
  Proof.
    intros.
    inversion H; subst; clear H.
    remember (decode_prog_input p) as q.
    destruct q as (M, w).
    inversion H1; subst; clear H1; run_simpl_all; intuition.
    inversion H3; subst; clear H3; intuition; run_simpl_all.
    intuition.
  Qed.

  (** Theorem 5.1 *)
  Theorem HALT_tm_undecidable:
    ~ Decidable HALT_tm.
  Proof.
    intros N.
    destruct N as (R, H).
    assert (Hx: Decidable A_tm). {
      apply decidable_def with (m:=HALT_tm_impl R).
      apply decides_def.
      + apply recognizes_impl with (L1:=HALT_tm_to_A_tm R); auto using halt_tm_mach_spec.
        unfold Equiv.
        intros.
        split; unfold HALT_tm_to_A_tm, A_tm; intros. {
          destruct (decode_prog_input i).
          intuition.
        }
        rename i into p.
        destruct (decode_prog_input p) as (M, w) eqn:Heq.
        split; auto.
        apply decides_accept with (L:=HALT_tm); auto.
        unfold HALT_tm.
        rewrite Heq.
        intros N.
        run_simpl_all.
      + unfold Decider.
        intros.
        intros N.
        apply halt_mach_loop in N.
        destruct (decode_prog_input i) as (M,w) eqn:Heqp.
        intuition.
        - assert (Hx: HALT_tm i). {
            eapply decides_run_accept; eauto.
          }
          unfold HALT_tm in Hx.
          rewrite Heqp in *.
          contradiction.
        - eapply decides_no_loop in H0; eauto.
    }
    apply a_tm_undecidable in Hx.
    assumption.
  Qed.

  End HALT_TM. (* ------------------------------------------------------------ *)

  Section E_TM. (* --------------------- Theorem 5.2 ------------------------- *)

  Definition E_tm : lang := fun p =>
    let M := decode_prog p in
    forall i, ~ Run M i Accept.

  (* We modify M to guarantee that M rejects all strings except w, but on input
     w it works as usual. *)
  Definition E_tm_M1 M w :=
    Read (fun x =>
      if input_eq_dec x w then (
        With w
        M
      ) else REJECT
    ).

  Lemma E_tm_M1_spec:
    forall M w,
    Recognizes (E_tm_M1 M w) (fun x => x = w /\ Run M w Accept).
  Proof.
    intros.
    unfold E_tm_M1.
    apply recognizes_def; intros i Ha.
    - inversion Ha; subst; clear Ha.
      destruct (input_eq_dec i w); run_simpl_all.
      intuition.
    - destruct Ha.
      subst.
      constructor.
      destruct (input_eq_dec w w). {
        repeat constructor; auto.
      }
      contradiction.
  Qed.

  (*
    The only string the machine can now accept is w, so its
    language will be nonempty iff it accepts w.
  *)
  Definition E_tm_A_tm (D:Prog) :=
    Read (fun p =>
      let (M, w) := decode_prog_input p in
      mlet b <- With [[ E_tm_M1 M w ]] D in
      halt_with (negb b)
    ).

  Definition E_tm_A_tm_spec : lang :=
    fun p =>
      let (M, w) := decode_prog_input p in
      ~ IsEmpty (E_tm_M1 M w).

  Lemma e_tm_reject_inv:
    forall D M,
    Decides D E_tm ->
    Run D [[ M ]] Reject ->
    ~ IsEmpty M.
  Proof.
    intros.
    apply decides_run_reject with (L:=E_tm) in H0; auto.
    intros N.
    unfold E_tm in *.
    rewrite decode_encode_prog_rw in *.
    unfold IsEmpty in *.
    contradict H0.
    intros.
    intros N1.
    assert (Hc: Run M i Accept) by auto using run_call.
    eapply recognizes_run_accept in Hc; eauto.
    contradiction.
  Qed.

  Lemma e_tm_reject:
    forall D M,
    Decides D E_tm ->
    ~ IsEmpty M ->
    Run D [[ M ]] Reject.
  Proof.
    intros.
    eapply run_call_decides_reject; eauto.
    intros N.
    unfold E_tm in N.
    contradict H0.
    unfold IsEmpty.
    split; intros.
    - assert (N := N i).
      run_simpl.
      contradiction.
    - contradiction.
  Qed.

  Lemma E_tm_A_tm_recognizes:
    forall D,
    Decides D E_tm ->
    Recognizes (E_tm_A_tm D) E_tm_A_tm_spec.
  Proof.
    intros.
    unfold E_tm_A_tm_spec, E_tm_A_tm, Recognizes.
    intros.
    rewrite run_read_rw.
    destruct (decode_prog_input i) as (M, w).
    split; intros.
    - inversion H0; subst; clear H0.
      rewrite run_with_rw in *.
      inversion H4; subst; clear H4. (* Dec r1 b *)
      run_simpl_all.
      apply e_tm_reject_inv in H3; auto. (* Run D [[ E_tm_M1 M w ]] Reject *)
    - apply run_seq_reject.
      + constructor.
        apply e_tm_reject; auto.
      + apply run_ret.
  Qed.

  Lemma not_accept_to_empty:
    forall M w,
    ~ Run M w Accept ->
    IsEmpty (E_tm_M1 M w).
  Proof.
    intros.
    rewrite is_empty_never_accept_rw.
    unfold NeverAccept.
    intros i N.
    unfold E_tm_M1 in *.
    run_simpl.
    destruct (input_eq_dec i w). {
      subst.
      run_simpl.
      contradiction.
    }
    run_simpl.
  Qed.

  Lemma not_empty_to_accept:
    forall M w,
    ~ IsEmpty (E_tm_M1 M w) ->
    Run M w Accept.
  Proof.
    intros.
    destruct (run_exists M w) as (r, Heqr).
    destruct r; auto.
    - contradict H.
      apply not_accept_to_empty.
      intros N.
      run_simpl_all.
    - contradict H.
      apply not_accept_to_empty.
      intros N.
      run_simpl_all.
  Qed.

  Lemma accept_to_not_empty:
    forall M w,
    Run M w Accept ->
    ~ IsEmpty (E_tm_M1 M w).
  Proof.
    intros.
    intros N.
    unfold E_tm_M1 in *.
    rewrite is_empty_never_accept_rw in *.
    unfold NeverAccept in *.
    apply (N w); auto.
    constructor.
    destruct (input_eq_dec w w).
    - constructor.
      assumption.
    - contradiction.
  Qed.

  Lemma e_tm_a_tm_spec:
    forall D,
    Decides D E_tm ->
    Recognizes (E_tm_A_tm D) A_tm.
  Proof.
    intros.
    apply recognizes_impl with (L1:=E_tm_A_tm_spec); auto using E_tm_A_tm_recognizes.
    unfold Equiv, E_tm_A_tm_spec, A_tm; split; intros;
    destruct (decode_prog_input i) as (M, w).
    - unfold E_tm in *.
      auto using not_empty_to_accept.
    - auto using accept_to_not_empty.
  Qed.

  Lemma decider_E_tm_A_tm:
    forall D,
    Decider D ->
    Decider (E_tm_A_tm D).
  Proof.
    unfold Decider, E_tm_A_tm.
    intros.
    intros N; subst.
    run_simpl.
    destruct (decode_prog_input _) as (M, w).
    inversion H1; subst; clear H1; run_simpl_all.
    apply H in H5.
    contradiction.
  Qed.

  Theorem E_tm_undecidable:
    ~ Decidable E_tm.
  Proof.
    intros HD.
    destruct HD as (R, H).
    assert (Hx: Decidable A_tm). {
      apply decidable_def with (m:=E_tm_A_tm R).
      apply decides_def.
      + auto using e_tm_a_tm_spec.
      + destruct H.
        auto using decider_E_tm_A_tm.
    }
    apply a_tm_undecidable in Hx.
    assumption.
  Qed.

End E_TM. (* --------------------------------------------------------------- *)

  Import Morphisms.
  Definition Reduction f (A B:lang) := forall w, A w <-> B (f w).

  Definition Reducible A B := exists f, Reduction f A B.

  Infix "<=m" := Reducible (at level 80, right associativity).

  Section CompFuncs.
    Global Instance reduction_equiv_proper f: Proper (Equiv ==> Equiv ==> iff) (Reduction f).
    Proof.
      unfold Proper, respectful.
      intros.
      split; intros;
      unfold Reduction in *; intros.
      - split; intros.
        + apply H in H2.
          apply H1 in H2.
          apply H0 in H2.
          assumption.
        + apply H0 in H2.
          apply H1 in H2.
          apply H.
          assumption.
      - split; intros.
        + apply H in H2.
          apply H1 in H2.
          apply H0 in H2.
          assumption.
        + apply H0 in H2.
          apply H1 in H2.
          apply H.
          assumption.
    Qed.

    Global Instance reducible_equiv_proper: Proper (Equiv ==> Equiv ==> iff) Reducible.
    Proof.
      unfold Proper, respectful.
      intros.
      split; intros;
      unfold Reducible in *; destruct H1 as (f, H1);
      exists f; rewrite H in *; rewrite H0 in *; assumption.
    Qed.

    Lemma reducible_def:
      forall f A B,
      Reduction f A B ->
      Reducible A B.
    Proof.
      intros.
      exists f.
      assumption.
    Qed.

    Lemma reducible_iff:
      forall f A B,
      (forall w, A w <-> B (f w)) ->
      Reducible A B.
    Proof.
      intros.
      exists f.
      assumption.
    Qed.

    Lemma co_red_co_1:
      forall A B,
      A <=m B ->
      compl A <=m compl B.
    Proof.
      intros.
      unfold Reducible in *.
      destruct H as (f, Hr).
      unfold Reduction in *.
      exists f.
      intros.
      unfold compl.
      split; intros.
      + intros N.
        apply Hr in N.
        contradiction.
      + intros N.
        apply Hr in N.
        contradiction.
    Qed.

    Lemma co_red_co_2:
      forall A B,
      compl A <=m compl B ->
      A <=m B.
    Proof.
      intros.
      unfold Reducible in *.
      destruct H as (f, Hr).
      unfold Reduction in *.
      exists f.
      intros.
      unfold compl.
      split; intros.
      + apply co_co_rw.
        intros N.
        apply Hr in N.
        contradiction.
      + apply co_co_rw.
        intros N.
        apply Hr in N.
        contradiction.
    Qed.

    Lemma co_red_co_rw:
      forall A B,
      compl A <=m compl B <-> A <=m B.
    Proof.
      split; auto using co_red_co_1, co_red_co_2.
    Qed.

    Lemma co_red_1:
      forall A B,
      compl A <=m B ->
      A <=m compl B.
    Proof.
      intros.
      assert (R: Equiv B (compl (compl B))) by (rewrite co_co_rw; reflexivity).
      rewrite R in H.
      rewrite co_red_co_rw in H.
      assumption.
    Qed.

    Lemma co_red_2:
      forall A B,
      A <=m compl B ->
      compl A <=m B.
    Proof.
      intros.
      assert (R: Equiv A (compl (compl A))) by (rewrite co_co_rw; reflexivity).
      rewrite R in H.
      rewrite co_red_co_rw in H.
      assumption.
    Qed.

    Theorem reducible_decidable: (*------------ Theorem 5.22 ---------------- *)
      forall A B,
      A <=m B ->
      Decidable B ->
      Decidable A.
    Proof.
      intros A B (f, Hred) (M, (Hr, Hd)).
      apply decidable_def with (m:=Read (fun w => With (f w) M)).
      split.
      - unfold Recognizes.
        split; intros. {
          run_simpl_all.
          apply Hred.
          apply Hr.
          assumption.
        }
        constructor.
        constructor.
        apply Hr.
        apply Hred.
        assumption.
      - unfold Decider in *.
        intros.
        intros N; subst.
        run_simpl_all.
        apply Hd in H4.
        contradiction.
    Qed.

    Theorem reducible_recognizable: (*------------ Theorem 5.28 ------------- *)
      forall A B,
      A <=m B ->
      Recognizable B ->
      Recognizable A.
    Proof.
      intros A B Hred Ha.
      unfold Recognizes in *.
      destruct Hred as (f, Hr).
      destruct Ha as (M, Ha).
      apply recognizable_def with (m:= Read (fun w => With (f w) M )).
      unfold Recognizes.
      split; intros. {
        run_simpl_all.
        apply Ha in H4.
        apply Hr in H4.
        assumption.
      }
      constructor.
      constructor.
      apply Hr in H.
      apply Ha.
      assumption.
    Qed.

    Corollary reducible_undecidable: (* ---------- Corollary 5.29 ----------- *)
      forall A B,
      A <=m B ->
      ~ Decidable A ->
      ~ Decidable B.
    Proof.
      intros.
      intros Hd.
      contradict H0.
      eauto using reducible_decidable.
    Qed.

    Corollary reducible_unrecognizable: (* ---------- Theorem 5.28 ---------- *)
      forall A B,
      A <=m B ->
      ~ Recognizable A ->
      ~ Recognizable B.
    Proof.
      intros A B Hred Ha Hb.
      contradict Ha.
      eauto using reducible_recognizable.
    Qed.


  End CompFuncs.

  Section A_TM.

  (* ----------------------------------------------- *)

  (** Show that co-A_tm is unrecognizable.
      Proof originally by Yannick Forster. *)

  (* Define the language of programs that accept their own code. *)

  Definition SELF_tm := fun i =>
    Run (decode_prog i) i Accept.

  (* 1. Show that the complement of SELF is unrecognizable *)

  Lemma co_self_tm_unrecognizable:
    ~ Recognizable (compl SELF_tm).
  Proof.
    intros N.
    destruct N as (p, Hr).
    destruct (run_exists p (encode_prog p)) as (r, He).
    assert (Hx := He).
    destruct r.
    - eapply recognizes_run_accept in He; eauto.
      unfold compl, SELF_tm in *.
      contradict He.
      run_simpl_all.
      assumption.
    - eapply recognizes_run_reject in He; eauto.
      contradict He.
      unfold compl, SELF_tm.
      intros N.
      run_simpl_all.
    - eapply recognizes_run_loop in He; eauto.
      contradict He.
      unfold compl, SELF_tm.
      intros N.
      run_simpl_all.
  Qed.

  (* 3. Show that co-A_tm map-reduces to co-SELF_tm *)
  
  Lemma co_A_tm_co_self_tm_rw:
    forall i,
    compl A_tm <[ decode_prog i, i ]> <-> compl SELF_tm i.
  Proof.
    unfold A_tm, SELF_tm, compl; split; intros.
    - intros N1.
      contradict H.
      run_simpl.
      assumption.
    - intros N1.
      contradict H.
      run_simpl.
      assumption.
  Qed.

  Lemma co_a_tm_red_co_self_tm:
    compl SELF_tm <=m compl A_tm.
  Proof.
    intros.
    exists (fun i => <[ decode_prog i, i ]>).
    unfold Reduction.
    intros.
    rewrite co_A_tm_co_self_tm_rw.
    reflexivity.
  Qed.

  (* 4. Show that co-A_tm is unrecognizable via map-reducibility *)

  Theorem co_a_tm_unrecognizable:
    ~ Recognizable (compl A_tm).
  Proof.
    apply reducible_unrecognizable with (A:=compl SELF_tm).
    - apply co_a_tm_red_co_self_tm.
    - apply co_self_tm_unrecognizable.
  Qed.

  (* 5. Show that A_tm is undecidable via Theorem 4.22 *)
  Theorem a_tm_undecidable:
    ~ Decidable A_tm.
  Proof.
    intros N.
    apply dec_rec_co_rec in N.
    destruct N as (_, N).
    apply co_a_tm_unrecognizable; auto.
  Qed.


  (* -------------------------------------------------------------------------- *)

  End A_TM.

  Section EQ_TM.

    (** We formally define EQ_TM: *)
    Definition EQ_tm := fun p =>
      let (w1, w2) := decode_pair p in
      let M1 := decode_prog w1 in
      let M2 := decode_prog w2 in
      Equiv (Lang M1) (Lang M2).

    Definition F1 p :=
      let (M, w) := decode_prog_input p in
      let M1 : input := [[ REJECT ]] in
      let M2 : input := [[ With w M ]] in
      encode_pair (M1 , M2).

    Lemma co_a_tm_red_eq_tm:
      compl A_tm <=m EQ_tm.
    Proof.
      apply reducible_iff with (f:=F1).
      unfold F1, EQ_tm; split; intros.
      - unfold A_tm, compl, Equiv, Lang in *.
        destruct (decode_prog_input w) as (M, x) eqn:Heq.
        run_simpl_all.
        destruct (run_exists M x) as ([], Hr).
        + contradiction.
        + split; intros; run_simpl_all.
        + split; intros; run_simpl_all.
      - destruct (decode_prog_input w) as (M, x) eqn:Heq.
        run_simpl_all.
        intros N.
        unfold Equiv in *.
        assert (Hm: Run (With x M) w Accept). {
          unfold A_tm in *.
          rewrite Heq in *.
          constructor.
          assumption.
        }
        clear N.
        repeat rewrite decode_encode_prog_rw in *.
        apply H in Hm.
        inversion Hm.
    Qed.

    Let F2 p :=
      let (M, w) := decode_prog_input p in
      let M1 : input := [[ ACCEPT ]] in
      let M2 : input := [[ With w M ]] in
      encode_pair (M1 , M2).

    Lemma a_tm_red_eq_tm:
      A_tm <=m EQ_tm.
    Proof.
      apply reducible_iff with (f:=F2).
      unfold F2, EQ_tm; split; intros.
      - destruct (decode_prog_input w) as (M, x) eqn:Heq.
        run_simpl_all.
        unfold Equiv, Lang; split; intros; run_simpl_all.
        + constructor.
          unfold A_tm in *.
          rewrite Heq in *.
          assumption.
        + apply run_ret.
      - unfold A_tm.
        destruct (decode_prog_input w) as (M, x) eqn:Heq.
        run_simpl_all.
        unfold Equiv, Lang in *.
        assert (Ha: Run ACCEPT w Accept). {
          apply run_ret.
        }
        apply H in Ha.
        run_simpl_all.
        assumption.
    Qed.

    Theorem eq_tm_not_recognizable:
      ~ Recognizable EQ_tm.
    Proof.
      apply reducible_unrecognizable with (A:=compl A_tm); auto.
      - apply co_a_tm_red_eq_tm.
      - apply co_a_tm_not_recognizable.
    Qed.

    Theorem co_eq_tm_not_recognizable:
      ~ Recognizable (compl EQ_tm).
    Proof.
      apply reducible_unrecognizable with (A:=compl A_tm); auto.
      - rewrite co_red_co_rw.
        apply a_tm_red_eq_tm.
      - apply co_a_tm_not_recognizable.
    Qed.

    Theorem eq_tm_not_decidable:
      ~ Decidable EQ_tm.
    Proof.
      intros N.
      apply dec_rec_co_rec in N.
      destruct N as (N, _).
      apply eq_tm_not_recognizable in N.
      assumption.
    Qed.

  End EQ_TM.
