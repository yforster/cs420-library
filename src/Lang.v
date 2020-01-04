Require Coq.Strings.Ascii.
Require Coq.Lists.List.
Require Coq.Setoids.Setoid.
Require Coq.Relations.Relations.
Require Coq.Classes.Morphisms.
Require Util.

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

  Definition Void : language := fun w => False.

  (** Conversely, no word is in [Void]. *)

  Lemma void_not_in:
    forall w,
    ~ Void w.
  Proof.
    intros.
    unfold Void; intros N.
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

  (** Auxiliary lemma that lets us use app when the string is not directly in
      the form of [w1 ++ w2]. *)
  Lemma app_in_eq:
    forall (L1 L2:language) w1 w2 w3,
    L1 w1 ->
    L2 w2 ->
    w3 = w1 ++ w2 ->
    App L1 L2 w3.
  Proof.
    intros.
    subst.
    apply app_in; auto.
  Qed.

  Lemma app_in_inv:
    forall (L1 L2:language) w,
    App L1 L2 w ->
    exists w1 w2, w = w1 ++ w2 /\ L1 w1 /\ L2 w2.
  Proof.
    unfold App; intros.
    assumption.
  Qed.

  Lemma app_l_char_in:
    forall c (L:language) w,
    L w ->
    App (Char c) L (c :: w).
  Proof.
    intros.
    apply app_in_eq with (w1:=[c]) (w2:=w).
    + apply char_in.
    + assumption.
    + reflexivity.
  Qed.

  Lemma app_l_all_in:
    forall (L:language) w1 w2,
    L w2 ->
    App All L (w1 ++ w2).
  Proof.
    intros.
    apply app_in_eq with (w1:=w1) (w2:=w2).
    + apply all_in.
    + assumption.
    + reflexivity.
  Qed.

  Lemma app_r_all_in:
    forall (L:language) w1 w2,
    L w1 ->
    App L All (w1 ++ w2).
  Proof.
    intros.
    apply app_in_eq with (w1:=w1) (w2:=w2).
    + assumption.
    + apply all_in.
    + reflexivity.
  Qed.

  Lemma app_l_char_in_inv:
    forall c L w,
    App (Char c) L w ->
    exists w', w = c:: w' /\ L w'.
  Proof.
    intros.
    apply app_in_inv in H.
    destruct H as (w1, (w2, (?, (Ha, Hb)))).
    apply char_in_inv in Ha.
    subst.
    exists w2.
    auto.
  Qed.

  Lemma app_r_char_in_inv:
    forall c L w,
    App L (Char c) w ->
    exists w', w = w' ++ [c] /\ L w'.
  Proof.
    intros.
    apply app_in_inv in H.
    destruct H as (w1, (w2, (?, (Ha, Hb)))).
    apply char_in_inv in Hb.
    subst.
    exists w1.
    auto.
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

  Lemma equiv_refl:
    forall L,
    Equiv L L.
  Proof.
    split; intros; tauto.
  Qed.

  (** Register [Equiv] in Coq's tactics. *)
  Global Add Parametric Relation : language Equiv
    reflexivity proved by equiv_refl
    symmetry proved by equiv_sym
    transitivity proved by equiv_trans
    as r_equiv_setoid.

  Goal forall (L1 L2:language), Equiv L1 L2 -> Equiv L2 L1.
  Proof.
    intros.
    symmetry. (** We can apply symmetry in the goal. *)
    rewrite H. (** We can rewrite H in the goal. *)
    reflexivity. (** We can use reflexivity to conclude Equiv goals. *)
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

  Lemma app_in_equiv:
    forall L1 L2 L3 L4 w,
    Equiv L1 L3 ->
    Equiv L2 L4 ->
    App L1 L2 w ->
    App L3 L4 w.
  Proof.
    intros.
    apply app_in_inv in H1.
    destruct H1 as (w1, (w2, (?, (Ha, Hb)))).
    subst.
    apply app_in.
    + apply H; assumption.
    + apply H0. assumption.
  Qed.

  Lemma equiv_app:
    forall L1 L2 L3 L4,
    Equiv L1 L3 ->
    Equiv L2 L4 ->
    Equiv (App L1 L2) (App L3 L4).
  Proof.
    split; intros.
    - eapply app_in_equiv; eauto.
    - eapply app_in_equiv; eauto.
      + apply equiv_sym. assumption.
      + apply equiv_sym. assumption.
  Qed.

  Lemma union_in_equiv:
    forall L1 L2 L3 L4 w,
    Equiv L1 L3 ->
    Equiv L2 L4 ->
    Union L1 L2 w ->
    Union L3 L4 w.
  Proof.
    intros.
    destruct H1.
    - apply H in H1.
      apply union_in_l.
      assumption.
    - apply H0 in H1.
      apply union_in_r.
      assumption.
  Qed.

  Lemma equiv_union:
    forall L1 L2 L3 L4,
    Equiv L1 L3 ->
    Equiv L2 L4 ->
    Equiv (Union L1 L2) (Union L3 L4).
  Proof.
    split; intros.
    - eapply union_in_equiv; eauto.
    - eapply union_in_equiv; eauto.
      + apply equiv_sym. assumption.
      + apply equiv_sym. assumption.
  Qed.

  Section equiv_proper.
  Import Morphisms.
  (* Allow rewriting under App *)
  Global Instance app_equiv_proper: Proper (Equiv ==> Equiv ==> Equiv) App.
  Proof.
    unfold Proper.
    unfold respectful.
    intros.
    apply equiv_app; auto.
  Qed.
  (* Allow rewriting under Union *)
  Global Instance union_equiv_proper: Proper (Equiv ==> Equiv ==> Equiv) Union.
  Proof.
    unfold Proper.
    unfold respectful.
    intros.
    apply equiv_union; auto.
  Qed.

  Global Instance star_equiv_proper: Proper (Equiv ==> Equiv) Star.
    unfold Proper.
    unfold respectful.
    apply star_equiv.
  Qed.

  End equiv_proper.
  (** Relate [All] with [Star Any]. *)

  Lemma app_assoc_in:
    forall L1 L2 L3 s,
    App (App L1 L2) L3 s ->
    App L1 (App L2 L3) s.
  Proof.
    intros.
    apply app_in_inv in H.
    destruct H as (w1, (w2, (?, (Ha, Hb)))).
    subst.
    apply app_in_inv in Ha.
    destruct Ha as (w3, (w4, (?, (Ha, Hc)))).
    subst.
    rewrite <- app_assoc.
    auto using app_in.
  Qed.

  Lemma app_assoc_rw:
    forall L1 L2 L3,
    Equiv (App (App L1 L2) L3) (App L1 (App L2 L3)).
  Proof.
    split; intros;
      apply app_in_inv in H;
      destruct H as (w1, (w2, (?, (Ha, Hb))));
      subst.
    - apply app_in_inv in Ha.
      destruct Ha as (w3, (w4, (?, (Ha, Hc)))).
      subst.
      rewrite <- app_assoc.
      auto using app_in.
    - apply app_in_inv in Hb.
      destruct Hb as (w3, (w4, (?, (Hb, Hc)))).
      subst.
      rewrite app_assoc.
      auto using app_in.
  Qed.

  Lemma star_any_spec:
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

  Lemma pow_char_in_inv:
    forall c n w,
    Pow (Char c) n w ->
    w = Util.pow1 c n.
  Proof.
    induction n; intros.
    - inversion H; subst; clear H.
      reflexivity.
    - inversion H; subst; clear H.
      inversion H2; subst; clear H2.
      apply IHn in H1.
      subst.
      reflexivity.
  Qed.

  Lemma pow_char_cons:
    forall c n w,
    Pow (Char c) n w ->
    Pow (Char c) (S n) (c::w).
  Proof.
    intros.
    apply pow_cons with (w1:=[c]) (w2:=w).
    - assumption.
    - apply char_in.
    - reflexivity.
  Qed.

  Lemma pow_char_in:
    forall c n,
    Pow (Char c) n (Util.pow1 c n).
  Proof.
    induction n; intros.
    - apply pow_nil.
    - simpl.
      apply pow_cons with (w1:=[c]) (w2:=Util.pow1 c n).
      + assumption.
      + apply char_in.
      + reflexivity.
  Qed.

  Lemma pow_char_cons_inv:
    forall c n w,
    Pow (Char c) (S n) w ->
    exists w', w = c::w' /\ Pow (Char c) n w'.
  Proof.
    intros.
    inversion H; subst; clear H.
    inversion H2; subst; clear H2.
    exists w2.
    auto.
  Qed.

  Lemma pow_pow_in_inv:
    forall c1 c2 n1 n2 w,
    App (Pow (Char c1) n1) (Pow (Char c2) n2) w ->
    w = Util.pow1 c1 n1 ++ Util.pow1 c2 n2.
  Proof.
    intros.
    apply app_in_inv in H.
    destruct H as (w1, (w2, (?, (Ha, Hb)))).
    subst.
    apply pow_char_in_inv in Ha.
    apply pow_char_in_inv in Hb.
    subst.
    reflexivity.
  Qed.

  Lemma pow_pow_in_inv_eq:
    forall c1 c2 n1 n2 m1 m2,
    c1 <> c2 ->
    App (Pow (Char c1) n1) (Pow (Char c2) n2) (Util.pow1 c1 m1 ++ Util.pow1 c2 m2) ->
    n1 = m1 /\ n2 = m2.
  Proof.
    intros.
    apply pow_pow_in_inv in H0.
    assert (n1 = m1) by eauto using Util.pow1_app_inv_eq_1.
    subst.
    assert (n2 = m2) by eauto using Util.pow1_app_inv_eq_2.
    subst.
    intuition.
  Qed.
End Defs.

Declare Scope lang_scope.

Module LangNotations.
  Import Ascii.
  Notation "{}" := Void : lang_scope.
  Notation "[]" := Nil : lang_scope.
  Infix "++" := App (right associativity, at level 60) : lang_scope.
  Notation "a || b" := (Union a b) (at level 50, left associativity)  : lang_scope.
  Notation "x '*'" := (Star x) (at level 20) : lang_scope.
  Infix "^^" := Pow (right associativity, at level 20) : lang_scope.
  Infix "==" := Equiv (left associativity, at level 40) : lang_scope.
  Coercion Char: ascii >-> language.
End LangNotations.

Module Examples.
  Import Ascii.
  Import List.
  Import LangNotations.
  Import ListNotations.
  Import Util.
  Open Scope lang_scope.
  Open Scope char_scope. (* Ensure by default we are representing characters. *)

  (** Any string that ends with "a" *)
  Definition L1 : language := All ++ "a".

  (** Show that the notation above is equivalent to writing a more direct, yet
     more verbose notation: *)
  Lemma l1_spec:
    L1 == fun w => exists w', (w = w' ++ ["a"]) % list.
  Proof.
    unfold L1; split; intros.
    - apply app_in_inv in H.
      destruct H as (w1, (w2, (Hi, (Hj, Hk)))).
      subst.
      exists w1.
      apply char_in_inv in Hk.
      subst.
      reflexivity.
    - destruct H as (w, ?).
      subst.
      apply app_in.
      + apply all_in.
      + apply char_in.
  Qed.

  (** Show that string "a" is in L1. *)
  Goal L1 ["a"].
  Proof.
    unfold L1.
    (*
      When using LangNotations, [] now becomes language Nil. If you use []
      to represent the empty list, you will get the following error:
      
         The term "[]" has type "word -> Prop" while it is expected to have type "list ascii".
     
      To work around the issue use nil to represent the empty string.
     *)
    apply app_in_eq with (w1:=nil) (w2:=["a"]). (* When using lists use nil to represent  *)
    + apply all_in.
    + apply char_in.
    + auto.
  Qed.

  (** Show that the empty string is not in L1. *)
  Goal ~ L1 nil.
  Proof.
    unfold L1; intros N.
    apply app_in_inv in N.
    destruct N as (w1, (w2, (H1, (H2, H3)))).
    (* We gather that (H1) w1 ++ w2 is the empty string *) 
    (* However, from (H3) we get that w2 is ["a"] *)
    apply char_in_inv in H3.
    subst.
    (* We are not done, because we do not know what w1 is. Let us do a case
       analysis on w1. *)
    destruct w1.
    + inversion H1. (* use the explosion principle, from w2 *)
    + inversion H1. (* use the explosion principle, from w1 *)
  Qed.

  (** Show that string "bbba" is L1 *)

  Goal L1 ["b"; "b"; "b"; "a"].
  Proof.
    unfold L1.
    apply app_in_eq with (w1:=["b"; "b"; "b"]) (w2:=["a"]).
    - apply all_in.
    - apply char_in.
    - reflexivity.
  Qed.

  Definition L2 : language := fun w => length w = 2.

  (** Show that string "01" is in L2. *)
  Goal L2 ["0"; "1"].
  Proof.
    unfold L2.
    reflexivity.
  Qed.

  Definition L3 : language := "a" ++ All ++ "b".

  Lemma l3_spec:
    L3 == fun w => exists w', (["a"] ++ w' ++ ["b"] = w) % list.
  Proof.
    unfold L3; split; intros.
    - apply app_l_char_in_inv in H.
      destruct H as (w1, (?, Hw)).
      apply app_r_char_in_inv in Hw.
      destruct Hw as (w2, (?, _)).
      subst.
      simpl.
      exists w2.
      reflexivity.
    - destruct H as (w, ?).
      subst.
      simpl.
      apply app_l_char_in.
      apply app_l_all_in.
      apply char_in.
  Qed.

  (** We define the language in terms of the Pow and App combinators. *)

  Definition L4 := fun w => exists n, ("a" ^^ n ++ "b" ^^ n) w.

  (** We then show that this correspond to our expectation of when not using
      combinators: *)
  Lemma l4_spec:
    L4 == fun x => exists n, (pow1 "a" n ++ pow1 "b" n = x) % list.
  Proof.
    unfold L4; split; intros.
    - destruct H as (n, Hw).
      exists n.
      apply app_in_inv in Hw.
      destruct Hw as (w1, (w2, (?, (Ha, Hb)))).
      subst.
      apply pow_char_in_inv in Ha.
      apply pow_char_in_inv in Hb.
      subst.
      reflexivity.
    - destruct H as (n, H).
      subst.
      exists n.
      apply app_in.
      + apply pow_char_in.
      + apply pow_char_in.
  Qed.

  (** L4 accepts the empty string. *)
  Goal L4 nil.
  Proof.
    unfold L4.
    exists 0.
    apply app_in_eq with (w1:=nil) (w2:=nil).
    + apply pow_nil.
    + apply pow_nil.
    + reflexivity.
  Qed.

  (** L4 accepts a single a and a single b. *)
  Goal L4 ["a"; "a"; "b"; "b"].
  Proof.
    exists 2.
    apply app_in_eq with (w1:=["a"; "a"]) (w2:=["b"; "b"]).
    + apply pow_char_cons, pow_char_cons.
      apply pow_nil.
    + apply pow_char_cons, pow_char_cons.
      apply pow_nil.
    + reflexivity.
  Qed.

  Goal ~ L4 ["a"; "b"; "b"].
  Proof.
    unfold L4;
    intros N.
    destruct N as (n, N).
    (* Let us rearrange the string to be in terms of Util.pow1. *)
    assert (R: ["a"; "b"; "b"] = (pow1 "a" 1 ++ pow1 "b" 2) % list) by reflexivity.
    rewrite R in *; clear R.
    (* Our language is: a^n b^n = a^1 b^2, thus n = 1 and n = 2
       and we reach a contradiction. *) 
    apply pow_pow_in_inv_eq in N.
    - (* n = 1 and n = 2, contradiction *)
      destruct N.
      subst.
      inversion H0.
    - (* show that a = b *)
      intros M.
      inversion M.
  Qed.

  (** Show that this random string is not in L4 *)

  Goal ~ L4 ["c"; "a"; "r"].
  Proof.
    unfold L4.
    intros N.
    destruct N as (n, H).
    (* Since the left-hand side has a power, we can enforce that the first
       character has to be a 'a' if n > 0. Let us do a case analysis on n. *)
    destruct n. {
      apply app_in_inv in H.
      destruct H as (w1, (w2, (Hs, (Ha, Hb)))).
      (* Any power of 0 yields an empty string, so w1 = [] and w2 = [] *) 
      inversion Ha; subst.
      inversion Hb; subst.
      (* Thus "car" = "" which is a contradiction. *)
      inversion Hs.
    }
    apply app_in_inv in H.
    destruct H as (w1, (w2, (Hs, (Ha, Hb)))).
    (* Ha is: a ^ (S n) = w, so we know that w = a :: w' *)
    apply pow_char_cons_inv in Ha.
    destruct Ha as (w', (?, ?)).
    subst.
    (* Hs now says that on the lhs starts with c and rhs starts with a,
       contradiction. *)
    inversion Hs.
  Qed.
End Examples.
