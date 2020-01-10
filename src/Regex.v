Require Coq.Strings.Ascii.
Require Coq.Lists.List.
Require Coq.Arith.PeanoNat.
Require Coq.omega.Omega.
Require Import Util.
Require Import Lang.

Open Scope char_scope. (* Ensure by default we are representing characters. *)

Inductive regex :=
  | r_void
  | r_nil
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
      destruct H; auto using accept_union_l, accept_union_r.
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
      subst.
      auto using accept_any.
  Qed.

  (** Any word is in [ANY *] *)

  Lemma accept_any_star:
    forall w,
    w \in r_star r_any.
  Proof.
    intros.
    (* Same as w in Star (Accept ANY) *)
    apply r_star_rw.
    (* Show that this is the same as [Star Any] *)
    apply star_equiv_in with (L1:=Any).
    - apply equiv_sym.
      apply r_any_rw.
    - (* Same as [All] *)
      apply star_any_rw.
      (* All strings are in [All] *)
      auto using all_in.
  Qed.

End Sigma.

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



