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

  Definition negator solve_A :=
    Read (fun w =>
      mlet b <- Call solve_A <[ decode_prog w, w ]> in
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


  (** Theorem 4.11, pp 207 *)

  Theorem a_tm_undecidable:
    ~ Decidable A_tm.
  Proof.
    intros N.
    (* Suppose that D is a decider for A_TM. *)
    destruct N as (solve_A, is_dec).
    destruct is_dec as (Hrec, Hdec).
    (* Now we construct a new Turing machine [negator] with D as a subroutine. *)
    (* What happens when we run [negator] with its own description <negator> as
      input? *)
    destruct (run_exists (negator solve_A) [[negator solve_A]] ) as (r, He).
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

  (* -------------------------------------------------------------------------- *)

  Lemma a_tm_recognizable: Recognizable A_tm.
  Proof.
    apply recognizable_def with (m:=Read (fun p => 
      let (M, w) := decode_prog_input p in
      (* Calls program M with input w *)
      Call M w
      )
    ).
    unfold Recognizes, A_tm.
    intros.
    (* remove the read from lhs *)
    rewrite run_read_rw.
    (* remove the pair *)
    destruct (decode_prog_input i) as (p, j).
    (* remove the with from lhs *)
    rewrite run_call_rw.
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
    Halts M w.

  (** Theorem 5.1 *)
  Theorem HALT_tm_undecidable:
    ~ Decidable HALT_tm.
  Proof.
    intros N.
    destruct N as (solves_HALT, H).
    assert (Hx: Decidable A_tm). {
      apply decidable_def with (m:=Read (fun p =>
        let (M, w) := decode_prog_input p in
        mlet b <- solves_HALT in
        if b then Call M w else REJECT 
      )).
      apply decides_def. {
        unfold A_tm.
        constructor; intros Ha. {
          rewrite run_read_rw in *.
          destruct (decode_prog_input i) as (p, j) eqn:r1.
          inversion Ha; subst; clear Ha.
          inversion H3; subst; clear H3; run_simpl_all.
          assumption.
        }
        rewrite run_read_rw in *.
        destruct (decode_prog_input i) as (p, j) eqn:r1.
        eapply run_seq_cont; eauto using dec_accept. {
          apply decides_accept with (L:=HALT_tm); auto.
          unfold HALT_tm.
          rewrite r1.
          auto using halts_accept.
        }
        simpl.
        constructor.
        assumption.
      }
      apply halts_to_decider.
      intros.
      constructor.
      destruct (decode_prog_input i) as (p, j) eqn:r1.
      destruct decides_to_run_dec with (p:=solves_HALT) (L:=HALT_tm) (i:=i)
        as (r, (b, (Hr, Hd))); auto.
      eapply halts_seq; eauto.
      inversion Hd; subst; constructor.
      eapply decides_run_accept in Hr; eauto.
      unfold HALT_tm in *.
      rewrite r1 in *.
      assumption.
    }
    apply a_tm_undecidable in Hx.
    assumption.
  Qed.

End HALT_TM. (* ------------------------------------------------------------ *)

Section E_TM. (* --------------------- Theorem 5.2 ------------------------- *)

  Definition E_tm : lang := fun p =>
    let M := decode_prog p in
    (forall i, Run M i Reject \/ Run M i Loop).

  Theorem E_tm_undecidable:
    ~ Decidable E_tm.
  Proof.
    intros HD.
    destruct HD as (solve_E, H).
    apply a_tm_undecidable.
    apply decidable_def with (m:=
      Read (fun p =>
        let (M, w) := decode_prog_input p in
        mlet b <- Call solve_E [[ Read (fun x =>
          if input_eq_dec x w then (
            Call M w
          ) else REJECT
        ) ]] in
        halt_with (negb b)
    )).
    apply decides_def. {
      split; intros Hi. {
        (* Run implies in A_tm *)
        unfold A_tm.
        rewrite run_read_rw in *.
        destruct (decode_prog_input i) as (p, j) eqn:r1.
        inversion Hi; subst; clear Hi.
        run_simpl_all.
        eapply decides_run_reject in H5; eauto.
        destruct (run_exists p j) as (r, Heqr).
        destruct r; auto.
        - contradict H5.
          unfold E_tm.
          intros k.
          run_simpl_all.
          repeat rewrite run_read_rw.
          left.
          destruct (input_eq_dec k j). {
            subst.
            constructor; auto.
          }
          constructor.
        - contradict H5.
          intros k.
          run_simpl_all.
          repeat rewrite run_read_rw.
          destruct (input_eq_dec k j). {
            subst.
            right.
            constructor; auto.
          }
          left.
          constructor.
        }
        (* From A_tm show that it accepts. *)
        rewrite run_read_rw.
        unfold A_tm in *.
        destruct (decode_prog_input i) as (p, j).
        eapply run_seq_cont; eauto using dec_reject. {
          constructor.
          eapply decides_reject; eauto.
          intros He.
          assert (He := He j).
          run_simpl_all.
          repeat rewrite run_read_rw in *.
          destruct (input_eq_dec j j); try contradiction.
          (* Run with different results is a contradiction *)
          intuition; run_simpl_all.
        }
        constructor.
      }
      (* Prove that it halts *)
      apply halts_to_decider.
      intros i.
      constructor.
      destruct (decode_prog_input i) as (p, j) eqn:r1.
      destruct decides_to_run_dec with (i:=[[
        Read (fun x =>
          if input_eq_dec x j then
          Call p j else REJECT)
        ]])
        (p:=solve_E) (L:=E_tm) as (r, (b, (Ha, Hb))); auto. 
      eapply halts_seq; eauto using halts_halt_with.
      constructor.
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
        let M2 : input := [[ Call M w ]] in
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
        assert (Hm: Run (Call M x) w Accept). {
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
        let M2 : input := [[ Call M w ]] in
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

