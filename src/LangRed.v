Require Import Turing.
Require Import LangDec.

Module Reducibility (Tur: Turing).
  Import Tur.
  Module B := TuringBasics Tur.
  Import B.
  Module D := Decidability Tur.
  Import D.

  Section HALT_TM. (* ---------------------- Theorem 5.1 --------------------- *)

  Definition HALT_tm : lang := fun p =>
    let (M, w) := decode_machine_input p in
    run M w <> Loop.

  Local Definition HALT_tm_to_A_tm D : lang :=
    (fun p =>
      let (M, w) := decode_machine_input p in
      run D p = Accept /\ run M w = Accept
    ).

  Local Definition halt_mach D :=
    Build (fun p =>
      let (M, w) := decode_machine_input p in
      mlet b <- Call D p in
      if b then Call M w else REJECT 
    ).

  Local Lemma halt_tm_mach_spec:
    forall D,
    Recognizes (halt_mach D) (HALT_tm_to_A_tm D).
  Proof.
    unfold Recognizes.
    split; intros.
    - unfold HALT_tm_to_A_tm.
      unfold halt_mach in *.
      apply run_build in H.
      remember (decode_machine_input i).
      destruct p as (M, w).
      run_simpl_all.
      inversion H3; subst; clear H3; run_simpl_all.
      intuition.
    - unfold HALT_tm_to_A_tm in *.
      remember (decode_machine_input i).
      symmetry in Heqp.
      destruct p as (M, w).
      destruct H.
      unfold halt_mach.
      apply run_build.
      rewrite Heqp.
      apply run_seq_accept; auto using run_call_eq.
  Qed.

  Local Lemma halt_mach_loop:
    forall D p,
    run (halt_mach D) p = Loop ->
    let (M, w) := decode_machine_input p in
    (run D p = Accept /\ run M w = Loop) \/ run D p = Loop.
  Proof.
    intros.
    apply run_build in H.
    remember (decode_machine_input p) as q.
    destruct q as (M, w).
    inversion H; subst; clear H.
    - inversion H2; subst; clear H2.
      inversion H3; subst; clear H3.
      + inversion H5; subst; clear H5.
        symmetry in Heqq.
        symmetry in H0.
        auto.
      + inversion H5.
    - inversion H1; subst; clear H1.
      auto.
  Qed.

  (** Theorem 5.1 *)
  Theorem HALT_tm_undecidable:
    ~ Decidable HALT_tm.
  Proof.
    intros N.
    destruct N as (R, H).
    assert (Hx: Decidable A_tm). {
      apply decidable_def with (m:=halt_mach R).
      apply decides_def.
      + apply recognizes_impl with (L1:=HALT_tm_to_A_tm R); auto using halt_tm_mach_spec.
        unfold Equiv.
        intros.
        split; unfold HALT_tm_to_A_tm, A_tm; intros. {
          destruct (decode_machine_input i).
          intuition.
        }
        rename i into p.
        destruct (decode_machine_input p) as (M, w) eqn:Heq.
        split; auto.
        apply decides_accept with (L:=HALT_tm); auto.
        unfold HALT_tm.
        rewrite Heq.
        rewrite H0.
        intros N; inversion N.
      + unfold Decider.
        intros.
        intros N.
        apply halt_mach_loop in N.
        destruct (decode_machine_input i) as (M,w) eqn:Heqp.
        destruct N as [(Hx,Hy)|N].
        - apply H in Hx.
          unfold HALT_tm in Hx.
          rewrite Heqp in Hx.
          contradiction.
        - apply H in N.
          assumption.
    }
    apply a_tm_undecidable in Hx.
    assumption.
  Qed.

  End HALT_TM. (* ------------------------------------------------------------ *)

  Section E_TM. (* --------------------- Theorem 5.2 ------------------------- *)

  Definition E_tm : lang := fun p =>
    let M := decode_machine p in
    IsEmpty M.

  (* We modify M to guarantee that M rejects all strings except w, but on input
     w it works as usual. *)
  Local Definition E_tm_M1 M w :=
    Build (fun x =>
      if input_eq_dec x w then (
        Call M w
      ) else REJECT
    ).
  Local Definition E_tm_M1_lang M w : lang := fun x =>
    x = w /\ run M w = Accept.

  Local Lemma E_tm_M1_spec:
    forall M w,
    Recognizes (E_tm_M1 M w) (E_tm_M1_lang M w).
  Proof.
    intros.
    unfold Recognizes, E_tm_M1, E_tm_M1_lang; split; intros.
    - apply run_build in H.
      destruct (input_eq_dec i w). {
        run_simpl.
        intuition.
      }
      inversion H.
    - destruct H.
      subst.
      apply run_build.
      destruct (input_eq_dec w w). {
        auto using run_call_eq.
      }
      contradiction.
  Qed.

  (*
    The only string the machine can now accept is w, so its
    language will be nonempty iff it accepts w.
  *)
  Local Definition E_tm_A_tm D :=
    Build (fun p =>
      let (M, w) := decode_machine_input p in
      mlet b <- Call D <[ E_tm_M1 M w ]> in
      halt_with (negb b)
    ).

  Local Definition E_tm_A_tm_spec :=
    fun p =>
      let (M, w) := decode_machine_input p in
      ~ IsEmpty (E_tm_M1 M w).

  Local Lemma e_tm_reject_inv:
    forall D M,
    Decides D E_tm ->
    run D <[ M ]> = Reject ->
     ~ IsEmpty M.
  Proof.
    intros.
    apply decides_run_reject with (L:=E_tm) in H0; auto.
    unfold E_tm in *.
    rewrite decode_encode_machine_rw in *.
    assumption.
  Qed.

  Local Lemma E_tm_A_tm_recognizes:
    forall D,
    Decides D E_tm ->
    Recognizes (E_tm_A_tm D) E_tm_A_tm_spec.
  Proof.
    intros.
    unfold E_tm_A_tm_spec, E_tm_A_tm, Recognizes.
    split; intros.
    - apply run_build in H0.
      destruct (decode_machine_input i) as (M, w).
      intros N.
      run_simpl_all.
      apply e_tm_reject_inv in H1; auto.
    - apply run_build.
      destruct (decode_machine_input _) as (M, w).
      apply run_seq_reject.
      + apply run_call_eq.
        apply decides_reject with (L:=E_tm); auto.
        unfold E_tm.
        rewrite decode_encode_machine_rw.
        assumption.
      + apply run_ret.
  Qed.

  Local Lemma not_accept_to_empty:
    forall M w,
    run M w <> Accept ->
    IsEmpty (E_tm_M1 M w).
  Proof.
    intros.
    rewrite is_empty_never_accept_rw.
    unfold NeverAccept.
    intros x.
    intros N.
    unfold E_tm_M1 in *.
    apply run_build in N.
    destruct (input_eq_dec x w). {
      subst.
      run_simpl.
      contradiction.
    }
    inversion N.
  Qed.

  Local Lemma not_empty_to_accept:
    forall M w,
    ~ IsEmpty (E_tm_M1 M w) ->
    run M w = Accept.
  Proof.
    intros.
    remember (run M w) as r.
    symmetry in Heqr.
    destruct r; auto.
    - contradict H.
      apply not_accept_to_empty.
      intros N.
      rewrite N in *.
      inversion Heqr.
    - contradict H.
      apply not_accept_to_empty.
      intros N.
      rewrite N in *.
      inversion Heqr.
  Qed.

  Local Lemma accept_to_not_empty:
    forall M w,
    run M w = Accept ->
    ~ IsEmpty (E_tm_M1 M w).
  Proof.
    intros.
    intros N.
    unfold E_tm_M1 in *.
    rewrite is_empty_never_accept_rw in *.
    unfold NeverAccept in *.
    assert (N := N w).
    contradict N.
    apply run_build.
    destruct (input_eq_dec w w).
    - auto using run_call_eq.
    - contradiction.
  Qed.

  Local Lemma e_tm_a_tm_spec:
    forall D,
    Decides D E_tm ->
    Recognizes (E_tm_A_tm D) A_tm.
  Proof.
    intros.
    apply recognizes_impl with (L1:=E_tm_A_tm_spec); auto using E_tm_A_tm_recognizes.
    unfold Equiv, E_tm_A_tm_spec, A_tm; split; intros;
    destruct (decode_machine_input i) as (M, w).
    - unfold E_tm in *.
      auto using not_empty_to_accept.
    - auto using accept_to_not_empty.
  Qed.

  Local Lemma decider_E_tm_A_tm:
    forall D,
    Decider D ->
    Decider (E_tm_A_tm D).
  Proof.
    unfold Decider, E_tm_A_tm.
    intros.
    intros N.
    apply run_build in N.
    destruct (decode_machine_input _) as (M, w).
    inversion N; subst; clear N.
    - destruct b; inversion H5.
    - run_simpl.
      apply H in H4.
      assumption.
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


End Reducibility.