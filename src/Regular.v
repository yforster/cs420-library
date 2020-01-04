Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import Coq.Arith.PeanoNat.

Require Coq.Classes.RelationClasses.
Require Coq.Setoids.Setoid.
Require Coq.Relations.Relations.


Require Coq.omega.Omega.
Import ListNotations.
Require Import Lang.
Require Import Regex.
Require Import Util.

Section Defs.
  Inductive Regular: language -> Prop :=
  | regular_def:
    forall r l,
    Equiv (Accept r) l ->
    Regular l.
End Defs.

Section Props.
  Lemma union_regular:
    forall L1 L2,
    Regular L1 ->
    Regular L2 ->
    Regular (Lang.Union L1 L2).
  Proof.
    intros.
    inversion H; subst; clear H.
    inversion H0; subst; clear H0.
    apply regular_def with (r:=r_union r r0).
    split; intros.
    - inversion H0; subst; clear H0.
      + apply union_in_l.
        apply H1.
        assumption.
      + apply union_in_r.
        apply H.
        assumption.
    - destruct H0.
      + apply H1 in H0.
        apply accept_union_l.
        assumption.
      + apply H in H0.
        apply accept_union_r.
        assumption.
  Qed.
End Props.

Section Pumping.
  Import Omega.

  Inductive Pump L p (w:word) : Prop :=
  | pump_def:
    forall x y z,
    w = x ++ y ++ z ->
    y <> [] ->
    length (x ++ y) <= p ->
    (forall i, L (x ++ pow y i ++ z)) ->
    Pump L p w.

  Lemma rex_pump_to_pump:
    forall L r w,
    Equiv (Accept r) L ->
    RexPump r w ->
    Pump L (pumping_constant r) w.
  Proof.
    intros.
    inversion H0; subst; clear H0.
    apply pump_def with (x:=x) (y:=y) (z:=z); auto.
    intros.
    apply H.
    apply H4.
  Qed.

  Theorem pumping:
    forall L,
    Regular L ->
    exists p, p >= 1 /\
    forall w, L w ->
    length w >= p ->
    Pump L p w.
  Proof.
    intros.
    inversion H; subst; clear H.
    exists (pumping_constant r).
    split. {
      apply pumping_constant_ge_1.
    }
    intros.
    assert (RexPump r w). {
      apply rex_pumping.
      + apply H0.
        assumption.
      + omega.
    }
    apply rex_pump_to_pump; auto.
  Qed.

  (** We say that a word [w] and size [p] clogs a language [L] when
      no matter how we divide [w] into three parts, there is at least one pumped
      string not in the language. *)
  Definition Clogs (L:language) p w := 
    forall (x y z:word),
      w = x ++ y ++ z ->
      y <> [] ->
      length (x ++ y) <= p ->
      exists i,
      ~ L (x ++ (pow y i) ++ z).

  (**

  A language is clogged if we can find one word in language [L] that clogs [L].

   w \in L    |w| >= p    Wrench L p w
   -----------------------------------
            L clogged with p
  *)
  Inductive Clogged (L:language) p : Prop :=
  | clogged_word:
    forall w,
    L w ->
    length w >= p ->
    Clogs L p w ->
    Clogged L p.
  (** Clogged languages are not regular.
      We show that a language is not regular by clogging it for all p >= 1. *)
  Lemma not_regular:
    forall (L:language),
    (forall p, p >= 1 -> Clogged L p) ->
    ~ Regular L.
  Proof.
    intros.
    intros N.
    apply pumping in N.
    destruct N as (p, (Hle, Hw)).
    assert (H := H _ Hle).
    inversion H; subst; clear H.
    assert (Hw := Hw w H0 H1).
    inversion Hw; subst; clear Hw.
    assert (Hi: exists i, ~ L (x ++ (pow y i) ++ z)). {
      auto.
    }
    destruct Hi as (i, Hi).
    contradict Hi.
    auto.
  Qed.

End Pumping.

Module Examples.
  Import Omega.
  Import RegexNotations.
  Import LangNotations.
  Import Lang.
  Import Setoid.

  Open Scope lang_scope.

  (** Ends with "a" *)

  Lemma l1_is_reg:
    Regular Examples.L1.
  Proof.
    apply regular_def with (r:= ANY *r ++r "a").
    unfold Examples.L1.
    rewrite app_spec.
    rewrite char_spec.
    rewrite star_spec.
    rewrite any_spec.
    rewrite star_any_spec.
    reflexivity.
    (* Direct proof: *)
    (*
    apply app_spec.
    unfold Equiv; split; unfold Examples.L1; intros.
    - inversion H; subst; clear H.
      exists s1.
      inversion H3; subst; clear H3.
      reflexivity.
    - destruct H as (w, Hs).
      subst.
      apply accept_app with (s1:=w) (s2:=["a"]); auto.
      + apply accept_any_star.
      + auto using accept_char.
      *)
  Qed.

  (** Any string of length 2 *)

  Definition L2 : language := fun w => length w = 2.
  Lemma l2_is_reg:
    Regular L2.
  Proof.
    apply regular_def with (r:= ANY ++r ANY).
    unfold Equiv, L2; split; intros.
    - inversion H; subst.
      apply any_inv in H2.
      apply any_inv in H3.
      destruct H2 as (c1, ?).
      destruct H3 as (c2, ?).
      subst.
      reflexivity.
    - destruct s. {
        inversion H.
      }
      inversion H; subst; clear H.
      destruct s. {
        inversion H1.
      }
      inversion H1; subst; clear H1.
      destruct s. {
        simpl.
        apply accept_any_cons.
        apply accept_any.
      }
      inversion H0.
  Qed.

  (** Any string that starts with "a" and ends with "b". *)

  Lemma l3_is_reg:
    Regular Examples.L3.
  Proof.
    unfold Examples.L3.
    apply regular_def with (r:="a" ++r ANY *r ++r "b").
    repeat rewrite app_spec.
    repeat rewrite char_spec.
    rewrite star_spec.
    rewrite any_spec.
    rewrite star_any_spec.
    rewrite Lang.app_assoc_rw.
    reflexivity.
  Qed.

  Lemma l1_l3:
    Regular (Lang.Union Examples.L1 Examples.L3).
  Proof.
    apply union_regular.
    - apply l1_is_reg.
    - apply l3_is_reg.
  Qed.

  (** Irregular language *)
(*
   Definition L4 : language := fun x => exists n, pow1 "a" n ++ pow1 "b" n = x.
*)
  Lemma xyz_rw:
    forall (a:ascii) b p x y z,
    (
    length (x ++ y) <= p ->
    pow1 a p ++ pow1 b p = x ++ y ++ z ->
    exists n,
    (length (x ++ y) + n) % nat = p /\
    pow1 a (length x + (length y + n)) ++ pow1 b (length x + length y + n) = x ++ y ++ z
    ) % list.
  Proof.
    intros.
    apply le_to_plus in H.
    destruct H as (n, Hlen).
    exists n.
    split; auto.
    rewrite <- Hlen in H0.
    rewrite app_length in H0.
    rewrite plus_assoc.
    assumption.
  Qed.

  Lemma pow1_plus_xy:
    forall (a:ascii) z x n y,
    (
    pow1 a (length x + n) ++ z = x ++ y ->
    x = pow1 a (length x) /\ y = pow1 a n ++ z
    ) % list.
  Proof.
    induction x; intros.
    - simpl in *.
      rewrite H.
      auto.
    - simpl in *.
      inversion H; subst; clear H.
      apply IHx in H2.
      destruct H2.
      split; auto.
      rewrite <- H.
      reflexivity.
  Qed.

  Lemma l1_not_regular:
    ~ Regular Examples.L4.
  Proof.
    apply not_regular.
    intros.
    (* We pick our word: *)
    apply clogged_word with (w:=(pow1 "a" p ++ pow1 "b" p) % list).
    - unfold Examples.L4.
      exists p.
      apply app_in.
      + apply pow_char_in.
      + apply pow_char_in.
    - rewrite app_length.
      rewrite pow1_length.
      omega.
    - unfold Clogs.
      intros.
      (* Goal 3: *)
      exists 2.
      (* Open up the definition of membership in L1 *)
      unfold Examples.L4.
      (* We have that there is a word in L1 and we will reach a contradiction *)
      intros N.
      (* Break down some n *)
      destruct N as (n, N).
      (* We don't want pow in N, so we compute function pow with simpl: *)
      simpl in N.
      (* We start working on our assumption H0, this is the first step of the slides:
         There is some b such that lenght (x ++ y) + b = p *)
      apply xyz_rw in H0; auto.
      (* We no longer need the length, so we ignore that assumption with _ *)
      destruct H0 as (b, (_, Hb)).
      (* We now separate x, y, and z in Hb *)
      apply pow1_plus_xy in Hb.
      destruct Hb as (Hx, Hyz).
      symmetry in Hyz.
      rewrite <- app_nil_end in *.
      apply pow1_plus_xy in Hyz.
      destruct Hyz as (Hy, Hz).
      (* We now know what x, y, and z are.
         We are ready to rewrite them in N. *) 
      rewrite Hy in N.
      rewrite Hx in N.
      rewrite Hz in N.
      (* Next, we want to simplify all of our powers of a into a single base at the
         RHS of the equality in N, so that we get a^x b^y = a^v b^w *)
      (* First we normalize ++ *) 
      repeat rewrite app_assoc in *.
      (* Then, we eagerly join the terms with the same base *) 
      repeat rewrite pow1_plus in N.
      (* We can now conclude that we have x = y and y = w: *)
      apply pow_pow_in_inv_eq in N. {
        destruct N as (N1, N2).
        (* We replace one in the other so that there is no 'n' anymore. *) 
        subst.
        (* We note that the left-hand side of both parts match, so we can simplify
           it in both ends of the equality. First, we put each element in
           evidence. *)
        repeat rewrite <- plus_assoc in *.
        apply plus_inv_eq_r, plus_inv_eq_r in N2.
        (* We now have to show that |y| + b = b *)
        apply plus_inv_zero_l in N2.
        (* But we know that |y| >= 1, so we reach a contradiction *)
        destruct y. {
          contradiction.
        }
        inversion N2.
      }
      (* Show that a <> b: *)
      intros C; inversion C.
  Qed.
End Examples.
