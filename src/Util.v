Require Import Coq.Arith.Plus.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.
Require Coq.Strings.Ascii.
Import ListNotations.

Lemma le_plus_trans_rev:
  forall n m p : nat, n <= m -> n <= p + m.
Proof.
  intros.
  assert (R: p + m = m + p). {
    apply Nat.add_comm.
  }
  rewrite R.
  apply Plus.le_plus_trans.
  assumption.
Qed.

Lemma le_to_plus:
  forall x y,
  x <= y ->
  exists z, x + z = y.
Proof.
  intros.
  eauto with *.
Qed.

Lemma plus_inv_eq_r:
  forall n x y,
  n + x = n + y ->
  x = y.
Proof.
  intros.
  induction n.
  - simpl in H.
    assumption.
  - inversion H.
    apply IHn.
    assumption.
Qed.

Lemma plus_inv_zero_l:
  forall y x,
  x + y = y ->
  x = 0.
Proof.
  induction y; intros. {
    rewrite plus_comm in H.
    assumption.
  }
  destruct x. {
    simpl in *.
    reflexivity.
  }
  rewrite Nat.add_succ_r in H.
  inversion H; subst; clear H.
  apply IHy.
  assumption.
Qed.


(* -------------------------------------------------------------------------- *)

Lemma app_inv_eq_l:
  forall (A:Type) (x:list A) y z,
  x ++ y = x ++ z ->
  y = z.
Proof.
  intros.
  induction x.
  - simpl in *.
    assumption.
  - inversion H; subst; clear H.
    apply IHx.
    assumption.
Qed.

(* ------------------------------------------------------------------------- *)

Fixpoint pow {T} (l : list T) (n : nat) : list T :=
  match n with
  | 0 => []
  | S n' => l ++ pow l n' 
  end.

Lemma pow_plus: forall T (n m : nat) (l : list T),
  pow l (n + m) = pow l n ++ pow l m.
Proof.
  induction n; simpl; intros.
  - reflexivity.
  - simpl.
    rewrite IHn.
    repeat rewrite app_assoc.
    reflexivity.
Qed.


(* ------------------------------------------------------------------------- *)

(** x^n for a single character *)

Fixpoint pow1 {T} (c:T) n :=
  match n with
  | 0 => []
  | S n => c :: pow1 c n
  end.

Lemma pow1_length:
  forall {T} (c:T) n,
  length (pow1 c n) = n.
Proof.
  induction n.
  - reflexivity.
  - simpl.
    rewrite IHn.
    reflexivity.
Qed.

Lemma pow1_plus:
  forall {T} x y (c:T),
  pow1 c x ++ pow1 c y = pow1 c (x + y). 
Proof.
  induction x; intros.
  - simpl.
    reflexivity.
  - simpl.
    rewrite IHx.
    reflexivity.
Qed.

Lemma pow1_inv_eq:
  forall {T} (c:T) x y,
  pow1 c x = pow1 c y ->
  x = y.
Proof.
  induction x; intros.
  - destruct y. {
      reflexivity.
    }
    inversion H.
  - simpl in *.
    destruct y. {
      inversion H.
    }
    inversion H; subst; clear H.
    apply IHx in H1.
    subst.
    reflexivity.
Qed.

Lemma pow1_app_inv_eq_1:
  forall {T} (a b:T),
  a <> b ->
  forall x y v w,
  pow1 a x ++ pow1 b y = pow1 a v ++ pow1 b w ->
  x = v.
Proof.
  intros ? a b.
  induction x; intros. {
    simpl in *.
    destruct v; auto.
    destruct y; simpl in *;
      inversion H0; subst; clear H0.
    contradiction.
  }
  simpl in *.
  destruct v; simpl in *. {
    destruct w; inversion H0; subst; clear H0.
    contradiction.
  }
  inversion H0; subst; clear H0.
  apply IHx in H2.
  subst; reflexivity.
Qed.


Lemma pow1_app_inv_eq_2:
  forall {T} (a:T) w y z,
  w ++ pow1 a y = w ++ pow1 a z ->
  y = z.
Proof.
  intros.
  apply app_inv_eq_l in H.
  apply pow1_inv_eq in H.
  assumption.
Qed.

Lemma pow1_a_b_inv_eq:
  forall {T} (a b:T),
  a <> b ->
  forall x y v w,
  pow1 a x ++ pow1 b y = pow1 a v ++ pow1 b w ->
  x = v /\ y = w.
Proof.
  intros.
  assert (Hx := H0).
  apply pow1_app_inv_eq_1 in H0; auto.
  subst.
  apply pow1_app_inv_eq_2 in Hx.
  auto.
Qed.


  (* Utility function that generates a list of all naturals from (n - 1) down
     to zero. *)
  Fixpoint count n := match n with
  | S n => n :: count n
  | 0 => []
  end.

  (* A simple usage test. *)
  Goal count 10 = [9; 8; 7; 6; 5; 4; 3; 2; 1; 0]. auto. Qed.


  (* We know that any number less than m is in (count m). *) 
  Lemma in_count:
    forall m n,
    n < m ->
    List.In n (count m).
  Proof.
    induction m; intros. {
      inversion H.
    }
    inversion H; subst; clear H. {
      simpl.
      auto.
    }
    simpl.
    right.
    auto.
  Qed.

  (* Example: *)
  Goal In 3 (count 10). apply in_count. auto with *. Qed. 

  (** We now define a list of all ascii *)
  Import Ascii.

  Definition all_ascii := List.map ascii_of_nat (count 256).

  (** We show that every ascii is in the list. *)
  Lemma in_all_ascii:
    forall (a:ascii),
    List.In a all_ascii.
  Proof.
    intros.
    unfold all_ascii.
    rewrite in_map_iff.
    exists (nat_of_ascii a).
    rewrite ascii_nat_embedding.
    split; auto.
    apply in_count.
    auto using nat_ascii_bounded.
  Qed.