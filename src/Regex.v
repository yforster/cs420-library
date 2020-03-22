Require Coq.Strings.Ascii.
Require Coq.Lists.List.
Require Coq.Arith.PeanoNat.
Require Coq.omega.Omega.
Require Coq.Classes.Morphisms.
Require Import Util.
Require Import Lang.

Open Scope char_scope. (* Ensure by default we are representing characters. *)

Inductive regex :=
  | r_void: regex
  | r_nil: regex
  | r_char: Ascii.ascii -> regex
  | r_app: regex -> regex -> regex
  | r_union: regex -> regex -> regex
  | r_star: regex -> regex.

Declare Scope regex_scope.

(* Give also a more math-y notation *)

Module RegexNotations.
  Notation "x ';;' y" := (r_app x y) (at level 40, left associativity) : regex_scope.
  Notation "a '||' b" := (r_union a b) (at level 50, left associativity)  : regex_scope.
End RegexNotations.

Import List.ListNotations.
Import Ascii.
Import List.
Import RegexNotations.

(* Also give a notation for the next relation we are defining. *)
Reserved Notation "s \in re" (at level 80).
Open Scope regex_scope.
(* Rather than writing [Char "c"] we can write just "c" and Coq will convert it to [Char "c"]*)
Coercion r_char: ascii >-> regex.

Inductive Accept : regex -> list ascii -> Prop :=
  | accept_nil:
    [] \in r_nil

  | accept_char: forall (x:ascii),
    [x] \in r_char x

  | accept_app: forall s1 s2 s3 re1 re2,
    s1 \in re1 ->
    s2 \in re2 ->
    s3 = s1 ++ s2 ->
    (*--------------------*)
    s3 \in re1 ;; re2

  | accept_union_l: forall s1 re1 re2,
    s1 \in re1 ->
    (*----------------*)
    s1 \in re1 || re2

  | accept_union_r: forall re1 s2 re2,
    s2 \in re2 ->
   (*-------------------*)
    s2 \in re1 || re2

  | accept_star_nil: forall re,
    [] \in r_star re

  | accept_star_cons_neq: forall s1 s2 s3 re,
    s1 \in re ->
    s2 \in r_star re ->
    s3 = s1 ++ s2 ->
    s1 <> [] ->
    (*-----------------*)
    s3 \in r_star re

  where "s \in re" := (Accept re s).

(** Examples *)
Goal ["a"] \in "a".
Proof.
  apply accept_char.
Qed.

Goal ["a"] \in "a".
Proof.
  apply accept_char.
Qed.

Goal ["a"; "b"] \in "a" ;; "b".
Proof.
  apply accept_app with (s1:=["a"]) (s2:=["b"]).
  + apply accept_char.
  + apply accept_char.
  + reflexivity.
Qed.

Lemma accept_star_cons:
  forall s1 s2 s3 re,
  s1 \in re ->
  s2 \in r_star re ->
  s3 = s1 ++ s2 ->
  s3 \in r_star re.
Proof.
  intros.
  destruct s1; simpl in *; subst. {
    assumption.
  }
  apply accept_star_cons_neq with (s1:=a::s1) (s2:=s2); auto.
  intros N; inversion N.
Qed.

Lemma accept_star_eq:
  forall s re,
  s \in re ->
  s \in r_star re.
Proof.
  intros s re H.
  destruct s. {
    auto using accept_star_nil.
  }
  apply accept_star_cons with (s1:=a :: s) (s2:=[]);
  auto using accept_star_nil, app_nil_end.
Qed.

Lemma accept_cons:
  forall s r c,
  s \in r ->
  c :: s \in r_char c ;; r.
Proof.
  intros.
  apply accept_app with (s1:=[c]) (s2:=s); auto using accept_char.
Qed.

Lemma accept_app_star_skip:
  forall s r1 r2,
  s \in r2 ->
  s \in r_star r1;; r2.
Proof.
  intros.
  apply accept_app with (s1:=[]) (s2:=s).
  - apply accept_star_nil.
  - assumption.
  - reflexivity.
Qed.

Lemma accept_pow1:
  forall c i,
  pow1 c i \in r_star (r_char c).
Proof.
  induction i.
  - apply accept_star_nil.
  - simpl.
    apply accept_star_cons with (s1:=[c]) (s2:=pow1 c i).
    + apply accept_char.
    + assumption.
    + reflexivity.
Qed.

Lemma accept_pow:
  forall s r i,
  s \in r ->
  Util.pow s i \in r_star r.
Proof.
  induction i; intros.
  - apply accept_star_nil.
  - simpl.
    apply accept_star_cons with (s1:=s) (s2:=pow s i).
    + assumption.
    + auto.
    + reflexivity.
Qed.

Lemma accept_pow_char:
  forall c i,
  Util.pow [c] i \in r_star (r_char c).
Proof.
  intros.
  apply accept_pow.
  apply accept_char.
Qed.


Section Union.
  (** [regex] expects union to be a binary-operation. Let us define
      union in terms of a list of regular expressions, rather than just
      binary. *)

  Definition union l := List.fold_right (fun a c => r_union a c) r_void l.

  (** If any regex in [l] accepts the string [s], then [union l] accepts [s]. *)
  Lemma in_union:
    forall l s a,
    List.In a l ->
    s \in a ->
    s \in union l.
  Proof.
    unfold union; induction l; intros. {
      contradiction.
    }
    destruct H. {
      subst.
      simpl.
      auto using accept_union_l.
    }
    simpl.
    eauto using accept_union_r.
  Qed.

  (** If the string is accepted by the union, then there must be a regex that
      accepts it. *)
  Lemma union_inv:
    forall s l,
    s \in union l ->
    exists r, List.In r l /\ s \in r.
  Proof.
    induction l; intros. {
      simpl in *.
      inversion H.
    }
    simpl in *.
    inversion H; subst; clear H. {
      eauto.
    }
    apply IHl in H3.
    destruct H3 as (r, (Hi, Hs)).
    exists r; eauto.
  Qed.
End Union.

Section Rewrite.
  Lemma r_union_rw:
    forall r1 r2,
    Equiv (Accept (r1 || r2)) (Lang.Union (Accept r1) (Accept r2)).
  Proof.
    unfold Equiv; split; intros.
    - inversion H; subst; clear H; auto using union_in_l, union_in_r.
    - apply union_in_inv in H.
      destruct H; rewrite <- Lang.in_def in *; auto using accept_union_l, accept_union_r.
  Qed.

  Lemma r_app_rw:
    forall r1 r2,
    Equiv (Accept (r1 ;; r2)) (Lang.App (Accept r1) (Accept r2)).
  Proof.
    unfold Equiv; split; intros.
    - inversion H; subst; clear H.
      auto using app_in_eq.
    - apply app_in_inv in H.
      destruct H as (w1, (w2, (H1, (H2, H3)))).
      subst.
      rewrite <- Lang.in_def in *.
      eauto using accept_app.
  Qed.

  Lemma r_char_rw:
    forall c,
    Equiv (Accept (r_char c)) (Lang.Char c).
  Proof.
    split; intros.
    - inversion H; subst; clear H.
      apply char_in.
    - apply char_in_inv in H.
      subst.
      apply accept_char.
  Qed.

  Lemma r_nil_rw:
    Equiv (Accept r_nil) Nil.
  Proof.
    split; intros.
    - inversion H; subst.
      apply nil_in.
    - apply nil_in_inv in H.
      subst.
      apply accept_nil.
  Qed.

  Lemma r_void_rw:
    Equiv (Accept r_void) Void.
  Proof.
    split; intros.
    - inversion H.
    - inversion H.
  Qed.

  Lemma star_inv_cons:
    forall r c w, 
    c :: w \in r_star r ->
    exists w1 w2, w1 ++ w2 = w /\ c :: w1 \in r /\ w2 \in r_star r.
  Proof.
    intros.
    inversion H; subst.
    destruct s1. {
      contradiction.
    }
    simpl in *.
    inversion H3; subst; clear H3.
    eauto.
  Qed.

  Lemma empty_str_star_inv:
    forall s,
    s \in r_star r_nil ->
    s = [].
  Proof.
    intros.
    inversion H; subst; auto.
    inversion H1; subst.
    contradiction.
  Qed.

  (** Concatenate the regex R n-times. *)
  Fixpoint r_pow r n :=
    match n with
    | 0 => r_nil
    | S n => r ;; r_pow r n  
    end.

  Lemma r_pow_succ:
    forall r n s1 s2,
    s1 \in r ->
    s2 \in r_pow r n ->
    s1 ++ s2 \in r_pow r (S n).
  Proof.
    intros.
    simpl.
    apply accept_app with (s1:=s1) (s2:=s2); auto.
  Qed.

  (** For any string [s] we can duplicate regex R n-times which will also accept
      [s].*)

  Lemma r_star_to_pow:
    forall r s,
    Accept (r_star r) s ->
    exists n, Accept (r_pow r n) s.
  Proof.
    intros.
    remember (r_star r) as r1.
    generalize dependent r.
    induction H; intros; inversion Heqr1; subst; clear Heqr1.
    - exists 0.
      apply accept_nil.
    - assert (Hx := IHAccept2 r).
      destruct Hx as (n, Hr); auto.
      eauto using r_pow_succ.
  Qed.

  Lemma r_pow_to_pow:
    forall n s r,
    s \in r_pow r n ->
    Pow (Accept r) n s.
  Proof.
    induction n; intros; simpl in *.
    - inversion H; subst.
      constructor.
    - inversion H; subst; clear H.
      apply IHn in H3.
      eapply pow_cons; eauto.
  Qed.

  Lemma r_star_rw:
    forall r,
    Equiv (Accept (r_star r)) (Lang.Star (Accept r)).
  Proof.
    split; intros.
    - apply r_star_to_pow in H.
      destruct H as (n, Hp).
      apply pow_to_star with (n:=n).
      apply r_pow_to_pow; assumption.
    - destruct H as (n, Hp).
      induction Hp. {
        apply accept_star_nil.
      }
      eapply accept_star_cons; eauto.
  Qed.
End Rewrite.

Section Sigma.
  (** We now define the set of all characters, know in the literature as 
      \Sigma. In Coq we represent it using [ascii], to encode it as a list,
      we have [all_ascii]. We build a regex that represents any character. *)

  (** Let us build a list with all possible characters. *)

  Definition all_chars := List.map r_char all_ascii.

  (** All characters are in the list. *)

  Lemma in_all_char:
    forall c,
    List.In (r_char c) all_chars.
  Proof.
    intros.
    unfold all_chars.
    rewrite in_map_iff.
    exists c.
    split; auto using in_all_ascii.
  Qed.

  (** All members of [all_char] are characters.*)

  Lemma all_chars_inv:
    forall r,
    In r all_chars ->
    exists c, r = r_char c.
  Proof.
    unfold all_chars; intros.
    rewrite in_map_iff in *.
    destruct H as (x, (Hc, Hi)).
    subst.
    exists x.
    reflexivity.
  Qed.

  (** Finally we are ready to define \Sigma *)
  Definition r_any : regex := union all_chars.


  (** Show that any single character is accepted by ANY *)
  Lemma accept_any:
    forall a,
    [a] \in r_any.
  Proof.
    intros.
    unfold r_any.
    apply in_union with (a:=r_char a); auto using in_all_char, accept_char.
  Qed.

  (** Useful lemma when trying to simplify strings. *)

  Lemma accept_any_cons:
    forall a r s,
    s \in r ->
    a :: s \in r_any ;; r.
  Proof.
    intros.
    apply accept_app with (s1:=[a]) (s2:=s); auto using accept_any.
  Qed.

  (** And the converse also holds, any string matched by ANY must be a
      character. *)
  Lemma accept_any_inv:
    forall s,
    s \in r_any ->
    exists c, s = [c].
  Proof.
    intros.
    unfold r_any in *.
    apply union_inv in H.
    destruct H as (r, (Hi, Hs)).
    apply all_chars_inv in Hi.
    destruct Hi as (c, Hi).
    subst.
    inversion Hs; subst.
    eauto.
  Qed.

  (** Any is a regular expression *)

  Lemma r_any_rw:
    Equiv (Accept r_any) Any.
  Proof.
    split; intros.
    - apply accept_any_inv in H.
      destruct H as (c, ?).
      subst.
      apply any_in.
    - apply any_in_inv in H.
      destruct H as (c, ?).
      rewrite <- Lang.in_def.
      subst.
      auto using accept_any.
  Qed.

  (** Any word is in [r_all] *)

  Definition r_all : regex := r_star r_any.

  Lemma r_all_rw:
    Equiv (Accept r_all) All.
  Proof.
    unfold r_all.
    rewrite r_star_rw.
    rewrite r_any_rw.
    rewrite star_any_rw.
    reflexivity.
  Qed.

  Lemma r_all_in:
    forall w,
    w \in r_all.
  Proof.
    intros.
    apply r_all_rw.
    apply all_in.
  Qed.

  Lemma accept_app_eq:
    forall s1 s2 re1 re2,
    s1 \in re1 ->
    s2 \in re2 ->
    (s1 ++ s2) \in re1;; re2.
  Proof.
    intros.
    apply accept_app with (s1:=s1) (s2:=s2); auto.
  Qed.

  Lemma r_pow_rw:
    forall r n,
    Equiv (Accept (r_pow r n)) (Pow (Accept r) n).
  Proof.
    induction n; intros.
    - split; simpl; intros.
      + inversion H; subst; clear H.
        apply pow_nil.
      + inversion H; subst; clear H.
        apply accept_nil.
    - split; simpl; intros.
      + inversion H; subst; clear H.
        apply IHn in H3.
        apply pow_cons_eq; auto.
      + inversion H; subst; clear H.
        apply IHn in H1.
        apply accept_app_eq; auto.
  Qed.

End Sigma.

Definition REquiv x y := Equiv (Accept x) (Accept y).
Infix "<==>" := REquiv (at level 85, no associativity) : regex_scope.

Section REquiv.

  (** Allow rewriting under Accept *)

  Lemma r_equiv_sym:
    forall r1 r2,
    r1 <==> r2 ->
    r2 <==> r1.
  Proof.
    unfold REquiv.
    intros.
    apply Lang.equiv_sym.
    assumption.
  Qed.

  (** Equivalence is transitive. *)

  Lemma r_equiv_trans:
    forall r1 r2 r3,
    r1 <==> r2 ->
    r2 <==> r3 ->
    r1 <==> r3.
  Proof.
    unfold REquiv.
    intros.
    eapply Lang.equiv_trans; eauto.
  Qed.

  Lemma r_equiv_refl:
    forall r,
    r <==> r.
  Proof.
    unfold REquiv.
    intros.
    apply Lang.equiv_refl.
  Qed.

  (** Register [Equiv] in Coq's tactics. *)
  Global Add Parametric Relation : regex REquiv
    reflexivity proved by r_equiv_refl
    symmetry proved by r_equiv_sym
    transitivity proved by r_equiv_trans
    as r_equiv_setoid.

  Import Morphisms.
  Global Instance rw_equiv_proper: Proper (REquiv ==> eq ==> iff) Accept.
  Proof.
    unfold Proper.
    unfold respectful.
    intros.
    subst.
    split; intros.
    - apply H.
      assumption.
    - apply H.
      assumption.
  Qed.

  Global Instance r_app_equiv_proper: Proper (REquiv ==> REquiv ==> REquiv) r_app.
  Proof.
    unfold Proper.
    unfold respectful.
    unfold REquiv; intros.
    repeat rewrite r_app_rw.
    rewrite H.
    rewrite H0.
    reflexivity.
  Qed.

  (* Allow rewriting under r_union *)
  Global Instance r_union_equiv_proper: Proper (REquiv ==> REquiv ==> REquiv) r_union.
  Proof.
    unfold Proper.
    unfold respectful.
    intros.
    unfold REquiv in *.
    repeat rewrite r_union_rw.
    rewrite H.
    rewrite H0.
    reflexivity.
  Qed.

  (* Allow rewrite under r_star *)
  Global Instance r_star_equiv_proper: Proper (REquiv ==> REquiv) r_star.
  Proof.
    unfold Proper.
    unfold respectful.
    unfold REquiv; intros.
    repeat rewrite r_star_rw.
    rewrite H.
    reflexivity.
  Qed.

  Lemma r_union_assoc_rw:
    forall r1 r2 r3,
    r1 || (r2 || r3) <==> (r1 || r2) || r3.
  Proof.
    intros.
    unfold REquiv.
    repeat rewrite r_union_rw.
    apply union_assoc_rw.
  Qed.

  Lemma r_app_assoc_rw:
    forall r1 r2 r3,
    r1 ;; (r2 ;; r3) <==> (r1 ;; r2) ;; r3.
  Proof.
    intros.
    unfold REquiv.
    repeat rewrite r_app_rw.
    apply app_assoc_rw.
  Qed.

  Lemma r_union_sym_rw:
    forall r1 r2,
    r1 || r2 <==> r2 || r1.
  Proof.
    unfold REquiv.
    intros.
    repeat rewrite r_union_rw.
    apply union_sym_rw.
  Qed.

  Lemma r_union_dup_rw:
    forall r,
    r || r <==> r.
  Proof.
    unfold REquiv; intros.
    rewrite r_union_rw.
    apply union_dup_rw.
  Qed.

  Lemma r_app_r_void_rw:
    forall r,
    r ;; r_void <==> r_void.
  Proof.
    unfold REquiv.
    intros.
    rewrite r_app_rw, r_void_rw.
    apply app_r_void_rw.
  Qed.

  Lemma r_app_l_void_rw:
    forall r,
    r_void ;; r <==> r_void.
  Proof.
    unfold REquiv.
    intros.
    rewrite r_app_rw, r_void_rw.
    apply app_l_void_rw.
  Qed.

  Lemma r_app_l_nil_rw:
    forall r,
    r_nil ;; r <==> r.
  Proof.
    unfold REquiv.
    intros.
    rewrite r_app_rw.
    rewrite r_nil_rw.
    apply app_l_nil_rw.
  Qed.

  Lemma r_app_r_nil_rw:
    forall r,
    r ;; r_nil <==> r.
  Proof.
    unfold REquiv; intros.
    rewrite r_app_rw, r_nil_rw.
    apply app_r_nil_rw.
  Qed.

  Lemma r_union_r_void_rw:
    forall r,
    r || r_void <==> r.
  Proof.
    unfold REquiv; intros.
    rewrite r_union_rw, r_void_rw.
    apply union_r_void_rw.
  Qed.

  Lemma r_union_l_void_rw:
    forall r,
    r_void || r <==> r.
  Proof.
    unfold REquiv; intros.
    rewrite r_union_rw, r_void_rw.
    apply union_l_void_rw.
  Qed.

  Lemma r_union_r_all_rw:
    forall r,
    r || r_all <==> r_all.
  Proof.
    unfold REquiv.
    intros.
    rewrite r_union_rw.
    rewrite r_all_rw.
    apply union_r_all_rw.
  Qed.

  Lemma r_union_l_all_rw:
    forall r,
    r_all || r <==> r_all.
  Proof.
    unfold REquiv; intros.
    rewrite r_union_rw.
    rewrite r_all_rw.
    apply union_l_all_rw.
  Qed.

  Lemma r_app_star_rw:
    forall r,
    r_star r ;; r_star r <==> r_star r.
  Proof.
    unfold REquiv; intros.
    rewrite r_app_rw.
    rewrite r_star_rw.
    apply app_star_rw.
  Qed.

  Lemma r_star_star_rw:
    forall r,
    r_star (r_star r) <==> r_star r.
  Proof.
    intros.
    unfold REquiv.
    repeat rewrite r_star_rw.
    apply star_star_rw.
  Qed.

  Lemma r_star_nil_rw:
    r_star r_nil <==> r_nil.
  Proof.
    unfold REquiv; intros.
    rewrite r_star_rw.
    rewrite r_nil_rw.
    apply star_nil_rw.
  Qed.

  Lemma r_star_void_rw:
    r_star r_void <==> r_nil.
  Proof.
    unfold REquiv.
    rewrite r_star_rw.
    rewrite r_void_rw.
    rewrite r_nil_rw.
    apply star_void_rw.
  Qed.

  Lemma r_app_union_distr_l:
    forall r1 r2 r3,
    (r1 ;; r3) || (r2 ;; r3) <==> (r1 || r2) ;; r3.
  Proof.
    unfold REquiv.
    intros.
    repeat (first [ rewrite r_app_rw | rewrite r_union_rw ]).
    apply app_union_distr_l.
  Qed.

  Lemma r_pow_zero_rw:
    forall r,
    r_pow r 0 <==> r_nil.
  Proof.
    unfold REquiv; intros.
    rewrite r_pow_rw.
    rewrite r_nil_rw.
    apply pow_zero_rw.
  Qed.

  Lemma r_pow_succ_equiv:
    forall n r1 r2,
    r1 <==> r2 ->
    r_pow r1 n <==> r_pow r2 n ->
    r_pow r1 (S n) <==> r_pow r2 (S n).
  Proof.
    unfold REquiv; intros.
    repeat rewrite r_pow_rw in *.
    apply pow_succ_equiv; auto.
  Qed.

  (** A nil inside a star can be elided. *)

  Lemma r_star_union_nil_rw:
    forall r,
    r_star (r_nil || r) <==> r_star r.
  Proof.
    unfold REquiv.
    intros.
    repeat first [ rewrite r_star_rw | rewrite r_union_rw | rewrite r_nil_rw ].
    apply star_union_nil_rw.
  Qed.

End REquiv.

Section Size.
  Fixpoint size r :=
  match r with
  | r_void | r_nil | r_char _ => 1
  | r_app r1 r2 | r_union r1 r2 => 1 + (size r1) + (size r2)
  | r_star r => 1 + (size r)
  end.
End Size.

Section Pumping.

  (** The pumping lemma is of crucial importance to study regular languages,
      as it provides an effective method to identify non-regular languages. *)

  Fixpoint pumping_constant (re : regex) : nat :=
    match re with
    | r_void => 1 (* One state is sufficient to accept r_void *)
    | r_nil => 1  (* One state is sufficient to accept r_nil *)
    | r_char _ => 2  (* Two states are sufficient to accept r_char *)
    | r_app re1 re2 => pumping_constant re1 + pumping_constant re2
    | r_union re1 re2 => pumping_constant re1 + pumping_constant re2
    | r_star r => pumping_constant r
    end.

  Lemma pumping_constant_ge_1:
    forall re,
    pumping_constant re >= 1.
  Proof.
    induction re; simpl; auto using le_n, Plus.le_plus_trans.
  Qed.

  Lemma pumping_constant_neq_0:
    forall re,
    pumping_constant re <> 0.
  Proof.
    intros re H.
    induction re; simpl in H; try (inversion H; fail).
    - apply Plus.plus_is_O in H.
      destruct H; auto. 
    - apply Plus.plus_is_O in H.
      destruct H.
      auto.
    - auto.
  Qed.

  Lemma pow_pump:
    forall m s1 s2 re,
    s1 \in re ->
    s2 \in r_star re ->
    pow s1 m ++ s2 \in r_star re.
  Proof.
    induction m; intros; simpl. {
      assumption.
    }
    apply accept_star_cons with (s1:=s1) (s2:=pow s1 m ++ s2); auto.
    rewrite app_assoc.
    reflexivity.
  Qed.

  Inductive RexPump re w : Prop :=
  | rex_pump_def:
    forall x y z,
    w = x ++ y ++ z ->
    y <> [] ->
    length (x ++ y) <= pumping_constant re ->
    (forall m, x ++ pow y m ++ z \in re) ->
    RexPump re w.

  Lemma rex_pump_app_l:
    forall re1 re2 s1 s2,
    RexPump re1 s1 ->
    s2 \in re2 ->
    RexPump (re1 ;; re2) (s1 ++ s2).
  Proof.
    intros.
    inversion H; subst; clear H.
    rewrite <- app_assoc, <- app_assoc.
    apply rex_pump_def with (x:=x) (y:=y) (z:=z ++ s2).
    * reflexivity.
    * assumption.
    * simpl.
      apply Plus.le_plus_trans.
      assumption.
    * intros m.
      repeat rewrite app_assoc.
      apply accept_app with (s1:=x++pow y m++z) (s2:=s2); auto.
      repeat rewrite <- app_assoc.
      reflexivity.
  Qed.

  Lemma pump_app_r:
    forall re1 re2 s1 s2,
    RexPump re2 s2 ->
    s1 \in re1 ->
    length s1 <= pumping_constant re1 ->
    RexPump (re1 ;; re2) (s1 ++ s2).
  Proof.
    intros.
    inversion H; subst; clear H.
    rewrite app_assoc.
    apply rex_pump_def with (x:=s1++x) (y:=y) (z:=z).
    - reflexivity.
    - assumption.
    - simpl.
      repeat rewrite app_length in *.
      rewrite Plus.plus_assoc_reverse.
      apply Plus.plus_le_compat; auto.
    - intros m.
      apply accept_app with (s1:=s1) (s2:=x ++ pow y m ++ z); auto. 
      repeat rewrite <- app_assoc.
      reflexivity.
  Qed.

  Lemma rex_pump_union_l:
    forall re1 re2 s1,
    RexPump re1 s1 ->
    RexPump (re1 || re2) s1.
  Proof.
    intros.
    inversion H; subst; clear H.
    apply rex_pump_def with (x:=x) (y:=y) (z:=z).
    - reflexivity.
    - assumption.
    - simpl.
      apply Plus.le_plus_trans.
      assumption.
    - intros.
      apply accept_union_l.
      auto.
  Qed.

  Lemma rex_pump_union_r:
    forall re1 re2 s2,
    RexPump re2 s2 ->
    RexPump (re1 || re2) s2.
  Proof.
    intros.
    inversion H; subst; clear H.
    apply rex_pump_def with (x:=x) (y:=y) (z:=z).
    - reflexivity.
    - assumption.
    - simpl.
      apply le_plus_trans_rev.
      assumption.
    - intros.
      apply accept_union_r.
      auto.
  Qed.

  Lemma rex_pump_star_1:
    forall s1 s2 re,
    s1 \in re ->
    s2 \in r_star re ->
    s1 <> [] ->
    length s1 <= pumping_constant re ->
    RexPump (r_star re) (s1 ++ s2).
  Proof.
    intros.
    apply rex_pump_def with (x:=[]) (y:=s1) (z:=s2).
    * reflexivity.
    * intros N; subst.
      contradiction.
    * simpl.
      assumption.
    * intros.
      simpl.
      auto using pow_pump.
  Qed.

  Lemma rex_pump_star_2:
    forall re s1 s2,
    RexPump re s1 ->
    s2 \in r_star re ->
    RexPump (r_star re) (s1 ++ s2).
  Proof.
    intros.
    inversion H; subst; clear H.
    apply rex_pump_def with (x:=x)(y:=y)(z:=z++s2); simpl; auto.
    * repeat rewrite <- app_assoc; reflexivity.
    * intros.
      apply accept_star_cons with (s1:=x ++ pow y m ++ z) (s2:=s2); auto.
      repeat rewrite app_assoc.
      reflexivity.
  Qed.

  Import Omega.

  Lemma pumping_constant_inv_app_1:
    forall re1 re2 (s1 s2:word),
    pumping_constant re1 + pumping_constant re2 <= length (s1 ++ s2) ->
    pumping_constant re1 <= length s1 \/ 
         (pumping_constant re2 <= length s2 /\ length s1 <= pumping_constant re1).
  Proof.
    intros.
    rewrite app_length in *.
    omega.
  Qed.

  Lemma pumping_constant_inv_app_2:
    forall s1 re (s2:list ascii),
    pumping_constant re <= length (s1 ++ s2) ->
    s1 = [] \/ (s1 <> [] /\ length s1 <= pumping_constant re) \/ pumping_constant re <= length s1.
  Proof.
    intros.
    rewrite app_length in *.
    destruct s1. {
      intuition.
    }
    right.
    destruct (PeanoNat.Nat.lt_ge_cases (length (a :: s1)) (pumping_constant re)). {
      simpl in *.
      left.
      split. {
        intros N; inversion N.
      }
      auto using Nat.lt_le_incl. 
    }
    right.
    assumption.
  Qed.

  Lemma rex_pumping : forall re s,
    s \in re ->
    pumping_constant re <= length s ->
    RexPump re s.
  Proof.
    intros re s Hmatch.
    induction Hmatch; simpl; intros Hlen; try omega.
    - subst.
      destruct pumping_constant_inv_app_1 with (re1:=re1) (re2:=re2) (s1:=s1) (s2:=s2)
        as  [? | []];
        auto using rex_pump_app_l, pump_app_r.
    - assert (H : pumping_constant re1 <= length s1) by omega.
      auto using rex_pump_union_l.
    - assert (H : pumping_constant re2 <= length s2) by omega.
      auto using rex_pump_union_r.
    - inversion Hlen as [|?].
      apply pumping_constant_neq_0 in H.
      contradiction.
    - destruct pumping_constant_inv_app_2 with (s1:=s1) (re:=re) (s2:=s2) as [?|[[]| ?]];
        subst; auto using rex_pump_star_1, rex_pump_star_2.
  Qed.

End Pumping.

Section Props.

  Lemma r_pow_char_in_inv:
    forall n c w,
    w \in r_pow (r_char c) n ->
    w = pow1 c n.
  Proof.
    induction n; intros.
    - inversion H; subst; clear H.
      reflexivity.
    - inversion H; subst; clear H.
      apply IHn in H3.
      subst.
      inversion H2; subst; clear H2.
      reflexivity.
  Qed.

  Lemma r_star_r_char_in_inv:
    forall w c,
    w \in r_star (r_char c) ->
    exists n, w = pow1 c n.
  Proof.
    intros.
    apply r_star_to_pow in H.
    destruct H as (n, Hr).
    exists n.
    apply r_pow_char_in_inv in Hr.
    assumption.
  Qed.

  Fixpoint as_lang r :=
  match r with
  | r_void => Void
  | r_nil => Nil
  | r_char c => Char c
  | r_app r1 r2 => App (as_lang r1) (as_lang r2)
  | r_union r1 r2 => Union (as_lang r1) (as_lang r2)
  | r_star r => Star (as_lang r)
  end.

  Lemma as_lang_rw:
    forall r,
    Equiv (Accept r) (as_lang r).
  Proof.
    induction r; simpl.
    - rewrite r_void_rw.
      reflexivity.
    - rewrite r_nil_rw.
      reflexivity.
    - rewrite r_char_rw.
      reflexivity.
    - rewrite <- IHr1.
      rewrite <- IHr2.
      rewrite r_app_rw.
      reflexivity.
    - rewrite <- IHr2.
      rewrite <- IHr1.
      rewrite r_union_rw.
      reflexivity.
    - rewrite <- IHr.
      rewrite r_star_rw.
      reflexivity.
  Qed.

End Props.


Module Examples.
  Import Ascii.
  Import List.
  Import ListNotations.
  Import Util.
  Import LangNotations.
  Import RegexNotations.
  Open Scope lang_scope.
  Open Scope char_scope. (* Ensure by default we are representing characters. *)
  
  (** Any string that ends with "a" *)
  Definition R1 : regex := r_all ;; "a".

  (** Show that the notation above is equivalent to writing a more direct, yet
     more verbose notation: *)
  Lemma r1_spec:
    (Accept R1) == Lang.Examples.L1.
  Proof.
    unfold Lang.Examples.L1, R1.
    rewrite r_app_rw.
    rewrite r_all_rw.
    rewrite r_char_rw.
    reflexivity.
  Qed.

  (** Show that string "a" is in L1. *)
  Lemma a_in_r1: ["a"] \in R1.
  Proof.
    unfold R1.
    (*
      You will note that r_all is a *derived* construct, which is constructed
      in terms of applying star to the any regex.
      The any regex (\Sigma) is defined as the union of all possibly characters.
      As such, one must be careful handling r_all because it is not "opaque"
      as a data-type constructor.
      
      In short, to handle r_all you must use theorems.
     *)
    apply accept_app_eq with (s1:=[]) (s2:=["a"]). (* When using lists use nil to represent  *)
    + apply r_all_in.
    + apply accept_char.
  Qed.

  (** Show that we can rewrite under In *)
  Lemma a_in_r1_void: ["a"] \in (R1 || r_void).
  Proof.
    (* We recall that we can simplify the language by descarding {} *)
    Search (_ || r_void).
    (* r_union_r_void_rw: forall r : regex, r || r_void <==> r *)
    rewrite r_union_r_void_rw.
    (* We now prove using the shorter proof: *)
    apply a_in_r1.
  Qed.

  (** Show that the empty string is not in L1. *)
  Lemma nil_not_in_r1: ~ ([] \in R1).
  Proof.
    unfold R1; intros N.
    (* Since acceptance was inductively defined, we can
       use inversion directly in our assumptions. *)
    inversion N; subst; clear N.
    (* H4: [] = s1 ++ s2 *)
    (* From (H4) we can conclude that s1=[] and s2=[] *)
    destruct s1. {
      (* s1 = [] *)
      destruct s2. {
        (* s2 = [] *)
        (* Note that we now find our contradiction, since [] \in "a",
           which is impossible *)
        inversion H2.
      }
      (* s2 <> [] *)
      (* Note the absurd assumption H4: [] = a :: s2 *)
      inversion H4.
    }
    (* s1 <> [] *)
    (* Note the absurd assumption H4: [] = a :: s2 *)
    inversion H4.
  Qed.

  (** Show that string "bbba" is L1 *)

  Goal ["b"; "b"; "b"; "a"] \in R1.
  Proof.
    unfold R1.
    apply accept_app_eq with (s1:=["b"; "b"; "b"]) (s2:=["a"]).
    - apply r_all_in.
    - apply accept_char.
  Qed.

  Definition R2 : regex := r_any ;; r_any.

  Lemma r2_spec:
    (Accept R2) == Lang.Examples.L2.
  Proof.
    unfold R2.
    (* When comparing against languages, we can rewrite (Accept R) into
       each corresponding language combinator. *)
    rewrite r_app_rw in *.
    rewrite r_any_rw in *.
    (* Finally we are ready to conclude *)
    rewrite Examples.l2_spec.
    reflexivity.
  Qed.

  (** Show that string "01" is in L2. *)
  Goal ["0"; "1"] \in R2.
  Proof.
    unfold R2.
    apply accept_any_cons.
    apply accept_any.
  Qed.

  Definition R3 : regex := "a" ;; r_all ;; "b".

  Lemma r3_spec:
    Accept R3 == Examples.L3.
  Proof.
    unfold R3.
    repeat rewrite r_app_rw.
    repeat rewrite r_char_rw.
    rewrite r_all_rw.
    reflexivity.
  Qed.

  (** L4 cannot be described in terms of regex *)

End Examples.
