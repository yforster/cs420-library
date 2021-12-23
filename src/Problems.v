Require Coq.Classes.RelationClasses.
Require Coq.Relations.Relations.
Require Coq.Classes.Morphisms.

Require Import Coq.Setoids.Setoid.

Require Import Turing.Turing.
Require Import Turing.LangDec.
Require Import Turing.LangRed.

Section A_TM. (* ----------------------------------------------- *)

  (* -------------------------------------------------------------------------- *)

  Definition A_tm : lang := fun p =>
    let (M, w) := decode_prog_input p in
    Run M w Accept.

  (** If [d] recognizes A_tm and machine d runs <M,w> *)
  Lemma a_tm_run_reject:
    forall p,
    Recognizes p A_tm ->
    forall w M,
    Run p <[ M, w ]> Reject -> 
    ~ Run M w Accept.
  Proof.
    unfold A_tm.
    intros.
    intros N.
    apply recognizes_run_reject with (L:=A_tm) in H0; auto.
    unfold A_tm in H0.
    run_simpl_all.
    contradiction.
  Qed.

  Lemma a_tm_run_loop:
    forall d,
    Recognizes d A_tm ->
    forall w m,
    Run d <[ m, w ]> Loop -> 
    ~ Run m w Accept.
  Proof.
    intros.
    intros N; subst.
    apply recognizes_run_loop with (L:=A_tm) in H0; auto.
    unfold A_tm in H0.
    rewrite decode_encode_prog_input_rw in *.
    contradiction.
  Qed.

  Lemma a_tm_run_accept:
    forall d,
    Recognizes d A_tm ->
    forall w m,
    Run d <[ m, w ]> Accept -> 
    Run m w Accept.
  Proof.
    intros.
    apply recognizes_run_accept with (L:=A_tm) in H0; auto.
    unfold A_tm in *.
    run_simpl_all.
    assumption.
  Qed.

  (**
    This new TM calls D to determine what M does when the input to M is its own
    description <M, <M>>. Once D has determined this information, it does the
    opposite. That is, it rejects if M accepts and accepts if M does not accept.

    The following is a description of [negator].
      negator = “On input <M>, where M is a TM :
          1. Run D on input <M, <M>>.
          2. Output the opposite of what D outputs.
            That is, if D accepts, reject ;
            and if D rejects, accept.”
  *)

  Definition negator D :=
    Read (fun w =>
      mlet b <- With <[ decode_prog w, w ]> D in
      if b then REJECT
      else ACCEPT
    ).

  Lemma negator_accept:
    forall D,
    Run (negator D) [[negator D]] Accept ->
    Run D <[ negator D, [[negator D]] ]> Reject.
  Proof.
    unfold negator.
    intros.
    run_simpl_all.
    inversion H1; subst; clear H1.
    inversion H3; subst; clear H3;
    run_simpl_all.
    assumption.
  Qed.

  Lemma negator_reject:
    forall D,
    Run (negator D) [[negator D]] Reject ->
    Run D <[ negator D, [[negator D]] ]> Accept.
  Proof.
    unfold negator.
    intros.
    run_simpl_all.
    inversion H1; subst; clear H1;
    inversion H3; subst; clear H3;
    run_simpl_all; auto.
  Qed.

  Lemma negator_loop:
    forall D,
    Decider D ->
    ~ Run (negator D) [[negator D]] Loop.
  Proof.
    unfold negator.
    intros.
    intros N.
    run_simpl_all.
    inversion H1; subst; clear H1.
    - inversion H4; subst; run_simpl_all.
    - run_simpl_all.
      apply decider_no_loop in H5; auto.
  Qed.

  Lemma no_decides_a_tm:
    ~ exists m, Decides m A_tm.
  Proof.
    unfold not.
    (* We assume that A_TM is decidable and obtain a contradiction. *)
    intros N.
    (* Suppose that D is a decider for A_TM. *)
    destruct N as (D, is_dec).
    destruct is_dec as (Hrec, Hdec).
    (* Now we construct a new Turing machine [negator] with D as a subroutine. *)
    (* What happens when we run [negator] with its own description <negator> as
      input? *)
    destruct (run_exists (negator D) [[negator D]] ) as (r, He).
    assert (Hx := He).
    (* (Let us duplicate Heqr as we will need it later.) *)
    destruct r; subst.
    - apply negator_accept in He.
      eapply recognizes_run_reject in He; eauto.
      contradict He.
      unfold A_tm.
      run_simpl_all.
      assumption.
    - apply negator_reject in He.
      eapply recognizes_run_accept in He; eauto.
      (* He: Run (negator D) [[negator D]] accept *)
      unfold A_tm in *.
      run_simpl_all.
    - apply negator_loop in Hx; auto.
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

  Lemma a_tm_recognizable: Recognizable A_tm.
  Proof.
    apply recognizable_def with (m:=Read (fun p => 
      let (M, w) := decode_prog_input p in
      (* Set the input to be w *)
      With w
      (* Continue with M *)
      M
      )
    ).
    unfold Recognizes, A_tm.
    intros.
    (* remove the read from lhs *)
    rewrite run_read_rw.
    (* remove the pair *)
    destruct (decode_prog_input i) as (p, j).
    (* remove the with from lhs *)
    rewrite run_with_rw.
    reflexivity.
  Qed.


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


  (** *********************************************
      * Another proof of A_tm undecidable follows *
      *********************************************

      Show that A_tm is undecidable via map-reducibility to SELF_tm.
      Proof originally by Yannick Forster.
      
      This proof similar to Sipser's Theorem 6.5.
  *)

  (* Define the language of programs that accept their own code. *)

  Definition SELF_tm := fun i =>
    Run (decode_prog i) i Accept.

  (* 1. Show that the complement of SELF is unrecognizable.
  
    Proof.

    Assume by contradiction that some program p recognizes itself.
    Case analysis on the result of running the p on itself.
    
    1. ACCEPTS itself. (Recognizability) Since p recognizes co-SELF and
       p accepts itself, then p is in co-SELF.
       (Def of co-SELF) If p is in co-SELF and p recognizes co-SELF,
       then p must reject itself.

    2. REJECTS/LOOPS itself. (Recognizability) Since p recognizes co-SELF and
       p rejects/loops itself, then p is not in co-SELF.

       (Def of co-SELF) However, can also show that p IS in co-SELF:
       as we only need to show that p does not accept itself
       (which is given already). 
   *)

  Lemma co_self_tm_unrecognizable:
    ~ Recognizable (compl SELF_tm).
  Proof.
    intros N.
    destruct N as (p, Hr).
    (* By contradiction, assume that p recognizes co-SELF_TM *)
    destruct (run_exists p (encode_prog p)) as (r, He).
    assert (Hx := He). (* Let us duplicate assumption Hx *)
    destruct r.
    - (* If p accepts itself *)
      eapply recognizes_run_accept in He; eauto.
      (* That means that p is in co-SELF *)
      unfold compl, SELF_tm in *.
      (* Since p is in co-self, then p should reject itself, which is an absurd  *)
      contradict He.
      run_simpl_all.
      assumption.
    - (* P rejects itself *)
      eapply recognizes_run_reject in He; eauto.
      (* Thus, p is NOT in co-SELF *)
      contradict He.
      unfold compl, SELF_tm.
      intros N.
      (* Since p is in co-self, then p must accept itself, thus absurd *)
      run_simpl_all.
    - (* p loops with itself *)
      eapply recognizes_run_loop in He; eauto.
      (* thus p is in co-SELF *)
      contradict He.
      unfold compl, SELF_tm.
      run_simpl.
      (* if [[p]] is in co-SELF, then p accepts [[self]] *)
      intros N.
      (* p accepts and loops on itself *)
      run_simpl_all.
  Qed.

  (* 3. Show that co-A_tm map-reduces to co-SELF_tm *)

  Lemma co_a_tm_red_co_self_tm:
    compl SELF_tm <=m compl A_tm.
  Proof.
    intros.
    (* Supply the mapping: *)
    exists (fun i => <[ decode_prog i, i ]>).
    unfold Reduction.
    intros.
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

  (* 4. Show co-A_tm is unrecognizable.

     Proof via map-reducibility:
     - We know co-SELF is unrecognizable.
     - We know that co-SELF <= co-A.

   *)

  Theorem co_a_tm_unrecognizable:
    ~ Recognizable (compl A_tm).
  Proof.
    apply reducible_unrecognizable with (A:=compl SELF_tm).
    - apply co_a_tm_red_co_self_tm.
    - apply co_self_tm_unrecognizable.
  Qed.

  (* 5. A_tm is undecidable.

     Proof.

     We have shown that A_tm is recognizable
     we have shown that A_tm is not co-recognizable.
     Thus, A_tm cannot be decidable (Theorem 4.22).

   *)
  Theorem a_tm_undecidable_alt:
    ~ Decidable A_tm.
  Proof.
    intros N.
    apply dec_rec_co_rec in N.
    destruct N as (_, N).
    apply co_a_tm_unrecognizable; auto.
  Qed.


  (* -------------------------------------------------------------------------- *)

  End A_TM.


Section HALT_TM. (* ---------------------- Theorem 5.1 --------------------- *)

  Definition HALT_tm : lang := fun p =>
    let (M, w) := decode_prog_input p in
    Run M w Accept \/ Run M w Reject.

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
        auto.
      + assert (Hx: Recognizes R HALT_tm). {
          destruct H; auto.
        }
        apply halts_to_decider.
        intros.
        apply decides_to_halts with (i:=i) in H.
        unfold HALT_tm_impl.
        constructor.
        destruct (decode_prog_input i) as (M,w) eqn:Heqp.
        apply halts_to_run_dec in H.
        destruct H as (r, (b, (Hr, Hd))).
        eapply halts_seq; eauto.
        inversion Hd; subst.
        - constructor.
          eapply recognizes_run_accept  in Hr; eauto; clear Hx.
          unfold HALT_tm in *.
          rewrite Heqp in *.
          apply run_to_halts.
          auto.
        - constructor.
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
    intros.
    apply halts_to_decider.
    intros.
    unfold E_tm_A_tm.
    constructor.
    destruct (decode_prog_input _) as (M, w).
    apply decider_to_halts with (i:=[[E_tm_M1 M w]] ) in H.
    apply halts_to_run_dec in H.
    destruct H as (r, (b, (Hr, Hd))).
    eapply halts_seq; eauto.
    - constructor; auto.
    - apply halts_halt_with.
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

Section EQ_TM.
    (** Show that EQ_TM is unrecognizable and co-unrecognizable. *)

    (** We formally define EQ_TM: *)
    Definition EQ_tm := fun p =>
      let (w1, w2) := decode_pair p in
      let M1 := decode_prog w1 in
      let M2 := decode_prog w2 in
      forall i,
      Run M1 i Accept <-> Run M2 i Accept.

    Lemma co_a_tm_red_eq_tm:
      compl A_tm <=m EQ_tm.
    Proof.
      apply reducible_iff with (f:=fun p =>
        let (M, w) := decode_prog_input p in
        let M1 : input := [[ REJECT ]] in
        let M2 : input := [[ With w M ]] in
        encode_pair (M1 , M2)
      ).
      unfold EQ_tm; split; intros.
      - unfold A_tm, compl in *.
        destruct (decode_prog_input w) as (M, x) eqn:Heq.
        run_simpl_all.
        destruct (run_exists M x) as ([], Hr).
        + contradiction.
        + split; intros; run_simpl_all.
        + split; intros; run_simpl_all.
      - destruct (decode_prog_input w) as (M, x) eqn:Heq.
        run_simpl_all.
        intros N.
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

    Lemma a_tm_red_eq_tm:
      A_tm <=m EQ_tm.
    Proof.
      apply reducible_iff with (f:=fun p =>
        let (M, w) := decode_prog_input p in
        let M1 : input := [[ ACCEPT ]] in
        let M2 : input := [[ With w M ]] in
        encode_pair (M1 , M2)
      ).
      unfold EQ_tm; split; intros.
      - destruct (decode_prog_input w) as (M, x) eqn:Heq.
        run_simpl_all.
        split; intros; run_simpl_all.
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

    (** Theorem 5.30: EQ_TM is neither recognizable nor co-recognizable. *)

    Theorem eq_tm_not_recognizable: (** Theorem 5.30 *)
      ~ Recognizable EQ_tm.
    Proof.
      apply reducible_unrecognizable with (A:=compl A_tm); auto.
      - apply co_a_tm_red_eq_tm.
      - apply co_a_tm_not_recognizable.
    Qed.

    Theorem co_eq_tm_not_recognizable: (** Theorem 5.30 *)
      ~ Recognizable (compl EQ_tm).
    Proof.
      apply reducible_unrecognizable with (A:=compl A_tm); auto.
      - rewrite co_red_co_rw.
        apply a_tm_red_eq_tm.
      - apply co_a_tm_not_recognizable.
    Qed.

    Theorem eq_tm_not_decidable: (** Theorem 5.4 *)
      ~ Decidable EQ_tm.
    Proof.
      intros N.
      apply dec_rec_co_rec in N.
      destruct N as (N, _).
      apply eq_tm_not_recognizable in N.
      assumption.
    Qed.

End EQ_TM.
