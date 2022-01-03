
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

  Inductive RunPar : Prog -> Prog -> (par_result -> Prog) -> input -> result -> Prop :=
  | run_par_l:
    forall p q c r b i,
    Run p i (Halt b) ->
    Run q i Loop ->
    Run (c (pleft b)) i r ->
    RunPar p q c i r
  | run_par_r:
    (** If `p` loops and `q` terminates, then
       we run continuation `c` with `cright b`. *)
    forall p q c r b i,
    Run p i Loop ->
    Run q i (Halt b) ->
    Run (c (pright b)) i r ->
    RunPar p q c i r
  | run_par_both:
    (** If both `p` and `q` terminate, then
       we run continuation `c` with `pboth b1 b2`. *)
    forall p1 p2 c r b1 b2 i,
    Run p1 i (Halt b1) ->
    Run p2 i (Halt b2) ->
    Run (c (pboth b1 b2)) i r ->
    RunPar p1 p2 c i r
  | run_par_loop:
    (** If both `p` and `q` loop, then the whole thing loops. *)
    forall p q c i,
    Run p i Loop ->
    Run q i Loop ->
    RunPar p q c i Loop.

  Axiom run_par_rw:
    forall p q c i r,
    Run (Par p q c) i r <-> RunPar p q c i r.

  (** We define a notion for parallel sequencing. *)
  Notation "'plet' x <- e1 '\\' e2 'in' c" := (Par e1 e2 (fun (x:par_result) => c)) (at level 60, right associativity).


Section Defs.

  (* -------------------------------------------------------------------------- *)

  Lemma decidable_to_compl:
    forall L,
    Decidable L ->
    Decidable (compl L).
  Proof.
    intros.
    destruct H as (m, H).
    apply decidable_def with (m:=mlet b <- m in Ret (Halt (negb b))).
    apply decides_def.
    - unfold compl.
      split; intros. {
        intros N.
        assert (Run m i (Halt true)) by eauto using decides_accept.
        inversion H0; subst; clear H0.
        run_simpl_all.
      }
      assert (Run m i (Halt false)) by eauto using decides_reject.
      eapply run_seq_cont; eauto.
      constructor.
    - apply halts_to_decider.
      intros.
      destruct decides_to_run with (p:=m) (L:=L) (i:=i) as (b, Hr); auto.
      apply halts_seq with (b:=b); auto.
      constructor.
  Qed.

  Definition par_run (m1 m2:Prog) p :=
    forall i,
      (
        Run p i (Halt true) /\ Run m1 i (Halt true)
      ) \/ (
        Run p i (Halt false) /\ (Run m1 i (Halt false) \/ ~ Run m2 i Loop)
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

  Inductive DisjointResults: result -> result -> Prop :=
  | disjoint_accept_loop:
    DisjointResults (Halt true) Loop
  | disjoint_accept_reject:
    DisjointResults (Halt true) (Halt false)
  | disjoint_loop_accept:
    DisjointResults Loop (Halt true)
  | disjoint_reject_accept:
    DisjointResults (Halt false) (Halt true).

  Lemma par_mach_lang:
    forall m1 m2,
    (forall i r1 r2, Run m1 i r1 -> Run m2 i r2 -> DisjointResults r1 r2) ->
    Recognizes (par_mach m1 m2) (fun i => Run m1 i (Halt true)).
  Proof.
    unfold par_mach.
    intros m1 m2 Hr; intros.
    unfold Recognizes; intros.
    rewrite run_read_rw.
    rewrite run_par_rw in *.
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
        assert (Hd: DisjointResults Loop (Halt false)) by eauto.
        inversion Hd.
      * (* Both machines terminated at the same time *)
        destruct b1; run_simpl_all.
        assumption.
    + destruct (run_exists m2 i) as (r, He).
      destruct r as [ [] |].
      * (* Absurd case: both cannot accept *)
        assert (N: DisjointResults (Halt true) (Halt true)) by eauto.
        inversion N.
      * apply run_par_both with (b1:=true) (b2:=false);
        auto using run_ret.
      * eapply run_par_l; eauto.
        constructor.
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
    subst.
    repeat rewrite run_read_rw in *.
    destruct r as [ [] | ].
    - left; split; auto.
      rewrite run_par_rw in *.
      inversion He; subst; clear He.
      + destruct b; run_simpl_all.
        assumption.
      + destruct b; run_simpl_all.
        assert (N: DisjointResults Loop (Halt false)) by eauto.
        inversion N.
      + destruct b1; run_simpl_all.
        assumption.
    - right.
      left.
      split; auto.
      rewrite run_par_rw in *.
      inversion He; subst; clear He.
      + destruct b; run_simpl_all.
        auto.
      + destruct b; run_simpl_all.
        right.
        intros N.
        run_simpl_all.
      + destruct b1; run_simpl_all; auto.
    - right.
      right.
      split; auto.
      rewrite run_par_rw in *.
      inversion He; subst; clear He;
      try (destruct b; run_simpl_all; auto); auto.
      (* Impossible case, since Run (if b1 then ACCEPT else REJECT) i Loop *)
      destruct b1; run_simpl_all.
  Qed.

  Lemma par_run_exists:
    forall m1 m2,
    (forall i r1 r2, Run m1 i r1 -> Run m2 i r2 -> DisjointResults r1 r2) ->
    exists p,
      Recognizes p (fun i => Run m1 i (Halt true)) /\ par_run m1 m2 p.
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
    Run m1 i (Halt false) ->
    Run m2 i (Halt true).
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
    destruct r1 as [ [] | ].
    - apply H in H1.
      eapply co_recognizes_not_accept with (m:=m2) in H1; eauto.
      destruct r2 as [ [] | ]; try contradiction; constructor.
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
      intuition; eauto.
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

