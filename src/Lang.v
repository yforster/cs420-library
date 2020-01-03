Require Coq.Strings.Ascii.
Require Coq.Lists.List.

Open Scope char_scope. (* Ensure by default we are representing characters. *)

Section Defs.
  Import List.
  Import ListNotations.
  Import Ascii.

  Definition word := list ascii.

  (** A language is a predicate on words. We say that [w] is in language [L] if,
      and only if, [L w]. *)

  Definition language := word -> Prop.

  (** The language that accepts all strings. *)

  Definition All : language := fun w => True.

  (** Every word is in [All]. *)

  Lemma all_in:
    forall w,
    All w.
  Proof.
    intros.
    unfold All.
    apply I.
  Qed.

  (** The language that rejects all strings. *)

  Definition Null : language := fun w => False.

  (** Conversely, no word is in [Null]. *)

  Lemma null_not_in:
    forall w,
    ~ Null w.
  Proof.
    intros.
    unfold Null; intros N.
    contradiction.
  Qed.

  (** [Nil] only accepts empty strings. *)

  Definition Nil : language := fun w => w = [].

  Lemma nil_in:
    Nil [].
  Proof.
    reflexivity.
  Qed.

  Lemma nil_in_inv:
    forall w,
    Nil w ->
    w = [].
  Proof.
    unfold Nil; intros.
    assumption.
  Qed.

  (** [Char] accepts a single character. *)

  Definition Char c : language :=
    fun w => w = [c].

  Lemma char_in:
    forall (c:ascii),
    Char c [c].
  Proof.
    intros.
    unfold Char.
    reflexivity.
  Qed.

  Lemma char_in_inv:
    forall c w,
    Char c w ->
    w = [c].
  Proof.
    intros.
    assumption.
  Qed.

  (** [Any] accepts any single character. *)

  Definition Any: language := fun w => exists c, w = [c].

  Lemma any_in:
    forall c,
    Any [c].
  Proof.
    intros.
    exists c.
    reflexivity.
  Qed.

  Lemma any_in_inv:
    forall w,
    Any w -> exists c, w = [c].
  Proof.
    unfold Any; auto.
  Qed.

  (** Concatenation of strings *)

  Definition App (L1 L2:language) : language :=
    fun w => exists w1 w2, w = w1 ++ w2 /\ L1 w1 /\ L2 w2. 

  (** Show that if [w1] is in [L1] and [w2] is in [L2], then [w1 ++ w2] is in
      [App L1 L2]. *)

  Lemma app_in:
    forall (L1 L2:language) w1 w2,
    L1 w1 ->
    L2 w2 ->
    App L1 L2 (w1 ++ w2).
  Proof.
    unfold App; intros.
    eauto.
  Qed.

  Lemma app_in_inv:
    forall (L1 L2:language) w,
    App L1 L2 w ->
    exists w1 w2, w = w1 ++ w2 /\ L1 w1 /\ L2 w2.
  Proof.
    unfold App; intros.
    assumption.
  Qed.

  (** Union on languages *)

  Definition Union (L1 L2:language) : language :=
    fun w => L1 w \/ L2 w.

  Lemma union_in_l:
    forall (L1 L2:language) w,
    L1 w ->
    Union L1 L2 w.
  Proof.
    unfold Union.
    eauto.
  Qed.

  Lemma union_in_r:
    forall (L1 L2:language) w,
    L2 w ->
    Union L1 L2 w.
  Proof.
    unfold Union; eauto.
  Qed.

  Lemma union_in_inv:
    forall (L1 L2:language) w,
    Union L1 L2 w ->
    L1 w \/ L2 w.
  Proof.
    unfold Union; auto.
  Qed.

  (** Pow definition based on: https://en.wikipedia.org/wiki/Kleene_star *)

  Inductive Pow (L:language) : nat -> word -> Prop :=
  | pow_nil:
    Pow L 0 nil
  | pow_cons:
    forall n w1 w2 w3,
    Pow L n w2 ->
    L w1 ->
    w3 = w1 ++ w2 ->
    Pow L (S n) w3.

  Lemma pow_in_eq:
    forall (L:language) w,
    L w ->
    Pow L 1 w.
  Proof.
    intros.
    apply pow_cons with (w1:=w) (w2:=nil).
    + apply pow_nil.
    + assumption.
    + rewrite app_nil_r.
      reflexivity.
  Qed.

  (** Star definition based on https://en.wikipedia.org/wiki/Kleene_star *)

  Definition Star L : language := fun w => exists n, Pow L n w.

  Lemma star_in_nil:
    forall L,
    Star L nil.
  Proof.
    intros.
    exists 0.
    apply pow_nil.
  Qed.

  Lemma star_in_eq:
    forall (L:language) w,
    L w ->
    Star L w.
  Proof.
    intros.
    exists 1.
    apply pow_in_eq; auto.
  Qed.

  Lemma pow_to_star:
    forall (L:language) n w,
    Pow L n w ->
    Star L w.
  Proof.
    intros.
    exists n.
    assumption.
  Qed.

  (** Equivalence of languages *)

  Definition Equiv (L1 L2:language) : Prop := forall s, L1 s <-> L2 s. 

  (** Equivalence is symmetric. *)

  Lemma equiv_sym:
    forall L1 L2,
    Equiv L1 L2 ->
    Equiv L2 L1.
  Proof.
    unfold Equiv; split; intros; apply H; assumption.
  Qed.

  (** Equivalence is transitive. *)

  Lemma equiv_trans:
    forall L1 L2 L3,
    Equiv L1 L2 ->
    Equiv L2 L3 ->
    Equiv L1 L3.
  Proof.
    unfold Equiv; intros.
    rewrite H.
    rewrite H0.
    intuition.
  Qed.

  Lemma pow_equiv_in:
    forall L1 L2 n s,
    Equiv L1 L2 ->
    Pow L1 n s ->
    Pow L2 n s.
  Proof.
    intros.
    induction H0; intros.
    - apply pow_nil.
    - subst.
      apply pow_cons with (w1:=w1) (w2:=w2); auto.
      apply H.
      assumption.
  Qed.

  Lemma pow_equiv:
    forall (L1 L2:language),
    Equiv L1 L2 ->
    forall n,
    Equiv (Pow L1 n) (Pow L2 n).
  Proof.
    split; intros.
    + eauto using pow_equiv_in.
    + apply equiv_sym in H.
      eauto using pow_equiv_in.
  Qed.

  Lemma star_equiv:
    forall (L1 L2:language),
    Equiv L1 L2 ->
    Equiv (Star L1) (Star L2).
  Proof.
    split; intros.
    + unfold Star in *.
      destruct H0 as (n, Hp).
      eauto using pow_equiv_in.
    + destruct H0 as (n, Hp).
      unfold Star.
      exists n.
      apply equiv_sym in H.
      eauto using pow_equiv_in.
  Qed.

  Lemma star_equiv_in:
    forall L1 L2 s,
    Equiv L1 L2 ->
    Star L1 s ->
    Star L2 s.
  Proof.
    intros.
    apply star_equiv in H.
    apply H.
    assumption.
  Qed.

  (** Relate [All] with [Star Any]. *)

  Lemma any_equiv_star_any:
    Equiv (Star Any) All.
  Proof.
    split; intros.
    - apply all_in.
    - unfold Star.
      generalize dependent H.
      induction s; intros. {
        exists 0.
        apply pow_nil.
      }
      assert (All s) by auto using all_in.
      destruct IHs as (n, Hp); auto.
      exists (S n).
      apply pow_cons with (w1:=[a]) (w2:=s); auto using any_in.
  Qed.

End Defs.