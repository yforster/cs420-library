
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
  Parameter Par: prog -> prog -> (par_result -> prog) -> prog.

  (** We define a notion for parallel sequencing. *)
  Notation "'plet' x <- e1 '\\' e2 'in' c" := (Par e1 e2 (fun (x:par_result) => c)) (at level 60, right associativity).

  Inductive RunPar : prog -> prog -> (par_result -> prog) -> bool -> Prop :=
  | run_par_l:
    forall p q c r b,
    Run p b ->
    Loop q ->
    Run (c (pleft b)) r ->
    RunPar p q c r
  | run_par_r:
    (** If `p` loops and `q` terminates, then
       we run continuation `c` with `cright b`. *)
    forall p q c r b,
    Loop p ->
    Run q b ->
    Run (c (pright b)) r ->
    RunPar p q c r
  | run_par_both:
    (** If both `p` and `q` terminate, then
       we run continuation `c` with `pboth b1 b2`. *)
    forall p1 p2 c r b1 b2,
    Run p1 b1 ->
    Run p2 b2 ->
    Run (c (pboth b1 b2)) r ->
    RunPar p1 p2 c r
  .

  Axiom run_par_rw:
    forall p q c b,
    Run (Par p q c) b <-> RunPar p q c b.


Section Defs.

  (* -------------------------------------------------------------------------- *)

  Lemma decidable_to_compl:
    forall L,
    Decidable L ->
    Decidable (compl L).
  Proof.
    intros.
    destruct H as (p, H).
    apply decidable_def with (p:=fun i => mlet b <- p i in Ret (negb b)).
    apply decides_def.
    - unfold compl.
      split; intros. {
        intros N.
        assert (Run (p i) true) by eauto using decides_accept.
        inversion H0; subst; clear H0.
        run_simpl_all.
      }
      assert (Run (p i) false) by eauto using decides_not_in_to_run_false.
      eapply run_seq; eauto.
      constructor.
    - apply decider_def.
      intros.
      assert (Ha: Halt (p i)) by eauto using decides_to_halt.
      rewrite halt_rw in Ha.
      destruct Ha as (b, Ha).
      econstructor; eauto.
      constructor.
  Qed.

  Definition par_mach M1 M2 : input -> prog :=
    fun w =>
      plet b <- Call M1 w \\ Call M2 w in
      Ret (match b with
      | pleft true
      | pboth true _
      | pright false => true
      | _ => false
      end)
    .

  Definition Disjoint p1 p2 : Prop :=
    (Run p1 true /\ Negative p2)
    \/
    (Negative p1 /\ Run p2 true).

  Lemma disjoint_run_true_1_rw:
    forall p1 p2,
    Disjoint p1 p2 ->
    Negative p2 <-> Run p1 true.
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
    forall p1 p2,
    Disjoint p1 p2 ->
    Negative p1 <-> Run p2 true.
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
    (forall i, Disjoint (Call m1 i) (Call m2 i)) ->
    Recognizes (par_mach m1 m2) (fun i => Run (Call m1 i) true).
  Proof.
    unfold par_mach.
    intros m1 m2 Hr; intros.
    unfold Recognizes; intros.
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
        assert (Ha: Negative (Call m1 i)). { auto using negative_loop. }
        rewrite (disjoint_run_true_2_rw _ _ (Hr i)) in *.
        run_simpl_all.
      * (* Both machines terminated at the same time *)
        destruct b1; run_simpl_all.
        assumption.
    }
    destruct (halt_or_loop (Call m2 i)) as [He|Hl]. {
      assert (Run (Call m2 i) false). {
        rewrite halt_rw in *.
        destruct He as ([],He); auto.
        rewrite <- (disjoint_run_true_1_rw _ _ (Hr i)) in H.
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
    forall m1 m2 i,
    Disjoint (Call m1 i) (Call m2 i) ->
    Halt (Call m1 i) ->
    Halt (Call m2 i) ->
    exists b, Run (Call m1 i) b /\ Run (Call m2 i) (negb b).
  Proof.
    intros.
    rewrite halt_rw in *.
    destruct H0 as ([], Ha), H1 as ([], Hb); eauto.
    - erewrite <- disjoint_run_true_1_rw in Ha; eauto.
      run_simpl_all.
    - assert (Hr: Negative (Call m2 i)). { auto using negative_run_false. }
      erewrite disjoint_run_true_1_rw in Hr; eauto.
  Qed.

  Definition par_run (p1 p2 p:input -> prog) :=
    forall i,
      (
        Run (p i) true /\ Run (p1 i) true /\ Negative (p2 i)
      ) \/ (
        Run (p i) false /\ Negative (p1 i) /\ Run (p2 i) true
      ).

  Lemma par_run_spec:
    forall m1 m2,
    (forall i, Disjoint (Call m1 i) (Call m2 i)) ->
    par_run (fun i => Call m1 i) (fun i => Call m2 i) (par_mach m1 m2).
  Proof.
    intros m1 m2 Hr.
    unfold par_run.
    unfold par_mach in *.
    intros.
    destruct (run_true_or_negative (Call m1 i)) as [Ha|Hl]; subst. {
      left.
      assert (hn: Negative (Call m2 i)). {
        rewrite disjoint_run_true_1_rw; eauto.
      }
      split; auto.
      rewrite negative_alt_rw in hn.
      rewrite run_par_rw in *.
      destruct hn as [hn|hn].
      - eapply run_par_both; eauto.
        constructor.
      - eapply run_par_l; eauto.
        constructor.
    }
    right.
    assert (hr: Run (Call m2 i) true). {
      rewrite disjoint_run_true_2_rw in Hl; eauto.
    }
    split; auto.
    rewrite negative_alt_rw in *.
    rewrite run_par_rw in *.
    destruct Hl as [hl|hl].
    - eapply run_par_both; eauto.
      constructor.
    - eapply run_par_r; eauto.
      constructor.
  Qed.

  Lemma par_run_exists:
    forall m1 m2,
    (forall i, Disjoint (Call m1 i) (Call m2 i)) ->
    exists p,
      Recognizes p (fun i => Run (Call m1 i) true) /\ par_run (fun i => Call m1 i) (fun i => Call m2 i) p.
  Proof.
    intros.
    exists (fun i=> par_mach m1 m2 i).
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
    Run (m1 i) false ->
    Run (m2 i) true.
  Proof.
    eauto using
      recognizes_run_false_to_not_in,
      co_recognizes_not_in_to_run_true.
  Qed.

  Lemma recognizes_co_recognizes_disjoint:
    forall m1 m2 L,
    Recognizes m1 L ->
    Recognizes m2 (compl L) ->
    (forall i, Disjoint (m1 i) (m2 i)).
  Proof.
    intros.
    unfold Disjoint.
    destruct
      (run_true_or_negative (m1 i)) as [Ha|Ha],
      (run_true_or_negative (m2 i)) as [Hb|Hb];
      (* Two cases are trivial. *)
      auto.
    - (* We have L i *)
      assert (H_yes: L i) by (eapply recognizes_run_true_to_in; eauto).
      (* But we also have ~ L i *)
      contradict H_yes.
      eapply recognizes_run_true_to_in with (L:=compl L) in Hb; eauto.
    - assert (~ L i). {
        (* (m1, i) is negative, and m1 recognizes L, thus  ~ L i *) 
        eauto using recognizes_negative_to_not_in.
      }
      (* Since we have ~ L i and m2 recognizes L, thus (m2, i) returns true *)
      assert (Run (m2 i) true). { eapply co_recognizes_not_in_to_run_true; eauto. }
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
    destruct H as (f_pos, Hpos).
    destruct H0 as (f_neg, Hneg).
    destruct (code_of f_pos) as (m_pos, c_pos).
    destruct (code_of f_neg) as (m_neg, c_neg).
    destruct par_run_exists with (m1:=m_pos) (m2:=m_neg) as (mpar, (Hr,Hp)). {
      intros.
      apply recognizes_co_recognizes_disjoint with (m1:=Call m_pos) (m2:=Call m_neg) (L:=L); eauto.
      - unfold Recognizes in *.
        intros k.
        rewrite <- Hpos.
        rewrite (code_of_run_rw c_pos).
        reflexivity.
      - unfold Recognizes in *.
        intros k.
        rewrite <- Hneg.
        rewrite (code_of_run_rw c_neg).
        reflexivity.
    }
    apply decidable_def with (p:=mpar).
    apply decides_def.
    + unfold Recognizes.
      intros.
      rewrite (Hr i).
      rewrite (code_of_run_rw c_pos).
      rewrite (recognizes_accept_rw Hpos).
      reflexivity.
    + unfold Decider.
      intros.
      assert (Hp := Hp i).
      intuition; eauto using run_to_halt.
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

