Require Coq.Classes.RelationClasses.
Require Coq.Relations.Relations.
Require Coq.Classes.Morphisms.

Require Import Coq.Setoids.Setoid.

Require Import Turing.Turing.
Require Import Turing.LangDec.

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

