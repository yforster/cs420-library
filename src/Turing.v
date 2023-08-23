Require Import Coq.Setoids.Setoid.
Require Import Coq.Bool.Bool.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Arith.Cantor.
From Undecidability Require Import L_facts L.Datatypes.LNat  L.Datatypes.LBool Extract Eval.
From SyntheticComputability Require Import Models.CT.

  (** These are the assumptions of our theory: *)
  (** We leave the input and the machine as unspecified data types. *)
  Definition input := nat.
  Definition input_inhabited := 0.
  (** Equality over the input is decidable. *)
  Lemma input_eq_dec: forall x y: input, {x = y} + {x <> y}.
  Proof. apply PeanoNat.Nat.eq_dec. Qed.

  (** Let us say we have a function that can encode and decode a pair of
      inputs. *)
  Definition decode_pair : input -> (input * input) :=
    of_nat.

  Definition encode_pair: (input * input) -> input :=
    to_nat.

  Lemma decode_encode_pair_rw:
    forall p,
    decode_pair (encode_pair p) = p.
  Proof. apply cancel_of_to. Qed.

  Lemma encode_decode_pair_rw:
    forall w,
    encode_pair (decode_pair w) = w.
  Proof. apply cancel_to_of. Qed.

  (** A language is a function that given an input (a word) holds if, and only if,
      that word is in the language. Thus, [L w] is the same as saying $w \in L$.
    *)

  Definition lang := input -> Prop.

  Definition machine :=
    { s : term | closed s}.
  Coercion term_of_machine := @proj1_sig _ _ : machine -> term.

  (** We can run a machine and obtain its run result. *)
  Definition Exec: machine -> input -> bool -> Prop :=
    fun s n b => eval (app s (enc n)) (enc (if b then 0 else 1)).

  Lemma exec_fun: forall m i b1 b2,
    Exec m i b1 ->
    Exec m i b2 ->
    b1 = b2.
  Proof.
    intros m i b1 b2 H1 H2.
    apply bool_enc_inj.

  (*   rewrite <- H1' in H2'. *)
  (*   destruct b1, b2; cbn in *; firstorder congruence. *)
  (* Qed. *)
  Admitted.

  Definition exec_exists:
    forall m i,
    (exists b, Exec m i b) \/ (forall b, ~ Exec m i b).
  Proof.
  Admitted.
  (*   intros [s Hs] i. unfold Exec. cbn. *)
  (*   destruct (classic (exists t, app s (enc i) ⇓ t)) as [[t H] | H]. *)
  (*   - destruct (term_eq_dec t (enc true)). *)
  (*     + subst. left. exists true. exists (enc true). split. eauto. firstorder. *)
  (*     + left. exists false. exists t. split. eauto. firstorder congruence. *)
  (*   - right. intros ? ?. firstorder. *)
  (* Qed. *)

  Inductive prog :=
    (**
     `Seq p1 f`: run p1, if p1 terminates, then
     run (f r) where `r` is a boolean that states if p1
     accepted or rejected its input.
    *)
  | Seq: prog -> (bool -> prog) -> prog
    (**
      Calls a machine with a given input
      (see Universal Turing Machines)
     *)
  | Call: machine -> input -> prog
    (**
      This Turing Machine just accepts/loops/rejects without
      any further operation.
      *)
  | Ret: bool -> prog
  .

  (**
    These describe the axiomatic semantics of turing machines.
    We can run a program `p` and obtain a resul `r` with
    `Run p r`.
    *)
  Inductive Run: prog -> bool -> Prop :=
  | run_ret:
    (** We can directly return a result *)
    forall b,
    Run (Ret b) b
  | run_call:
    (** Run a turing machine `m`. *)
    forall m i b,
    Exec m i b ->
    Run (Call m i) b
  | run_seq:
    (** If `p` terminates and returns `b`, then we can
       proceed with the execution of `q b`. *) 
    forall p q b1 b2,
    Run p b1 ->
    Run (q b1) b2 ->
    Run (Seq p q) b2.

  Lemma run_seq_rw:
    forall p q b,
      Run (Seq p q) b <-> (
                          (exists b', Run p b' /\ Run (q b') b)
                        ).
  Proof.
    split; intros. {
      inversion_clear H.
      destruct b; exists b1; intuition.
    }
    destruct H as (b', (Ha,Hb)).
    econstructor; eauto.
  Qed.

  Lemma run_call_rw:
    forall m i b,
      Run (Call m i) b <-> Exec m i b.
  Proof.
    split; intros. {
      now inversion_clear H.
    }
    econstructor; eauto.
  Qed.

  Lemma run_ret_rw:
    forall b b',
      Run (Ret b) b' <-> b = b'.
  Proof.
    split; intros. {
      now inversion_clear H.
    }
    subst. econstructor.
  Qed.

  Inductive Halt : prog -> Prop :=
  | halt_ret:
    (** We can directly return a result *)
    forall b,
    Halt (Ret b)
  | halt_call:
    (** Run a turing machine `m`. *)
    forall m i b,
    Exec m i b ->
    Halt (Call m i)
  | halt_seq:
    (** If `p` terminates and returns `b`, then we can
       proceed with the execution of `q b`. *) 
    forall p q b,
    Run p b ->
    Halt (q b) ->
    Halt (Seq p q).

  Inductive Loop: prog -> Prop :=
  | loop_tur:
    (** Run a turing machine `m`. *)
    forall m i,
    (forall b, ~ Exec m i b) ->
    Loop (Call m i)
  | loop_seq_l:
    (** If `p` terminates and returns `b`, then we can
       proceed with the execution of `q b`. *) 
    forall p q,
    Loop p ->
    Loop (Seq p q)
  | loop_seq_r:
    (** If `p` terminates and returns `b`, then we can
       proceed with the execution of `q b`. *) 
    forall p q b,
    Run p b ->
    Loop (q b) ->
    Loop (Seq p q).

  Inductive Negative (p:prog) : Prop :=
  | negative_run_false:
    Run p false ->
    Negative p
  | negative_loop:
    Loop p ->
    Negative p.

  (** We define a notation for sequencing. *)
  Notation "'mlet' x <- e 'in' c" := (Seq e (fun x => c)) (at level 60, right associativity).

  Definition ClosureOf (f:input -> input -> prog) (c:input -> machine) :=
    forall param i b, Run (f param i) b <-> Exec (c param) i b.


  Axiom ct : CT_L.

  Import L_Notations.

  Fixpoint eqb (s t : term) {struct s} :=
    match s, t with
    | lam s, lam t => eqb s t
    | app s1 s2, app t1 t2 => eqb s1 t1 && eqb s2 t2
    | var n1, var n2 => Nat.eqb n1 n2
    | _, _ => false
    end.

  Lemma eqb_spec s t : reflect (s = t) (eqb s t).
  Proof.
    induction s in t |- *; destruct t; cbn; try (now econstructor; congruence).
    - destruct (Nat.eqb_spec n n0); econstructor; congruence.
    - destruct (IHs1 t1), (IHs2 t2); econstructor; congruence.
    - destruct (IHs t); econstructor; congruence.
  Qed.

  Fixpoint run (p : prog) (n : nat) : option nat :=
    match p with
    | Seq p c => match run p n with
                | Some 0 => run (c true) n
                | Some _ => run (c false) n
                | _ => None
                end
    | Call m i => match eva n (m (enc i)) with
                 | Some v => if eqb v (enc 0) then Some 0
                            else if eqb v (enc 1) then Some 1
                            else None
                 | None => None
                 end
    | Ret b => Some (if b then 0 else 1)
    end.

  Lemma run_mono p n1 n2 v :
    run p n1 = Some v -> n2 >= n1 -> run p n2 = Some v.
  Proof.
    induction p in n1, n2, v |- *; intros; cbn in *.
    - destruct (run p n1) as [ [] | ] eqn:E; try congruence.
      erewrite IHp; eauto. cbn. eauto.
      erewrite IHp; eauto. cbn. eauto.
    - destruct (eva n1) eqn:E; try congruence.
      erewrite Seval.eva_le; eauto.
    - eauto.
  Qed.

  Lemma run_typed p n v :
    run p n = Some v -> v = 0 \/ v = 1.
  Proof.
    intros H.
    induction p in n, v, H |- *; cbn in *.
    - destruct run as [ [] | ] eqn:E; try congruence; eauto.
    - destruct eva; try congruence.
      destruct (eqb_spec t (enc 0)); subst; try now firstorder congruence.
      destruct (eqb_spec t (enc 1)); subst; try now firstorder congruence.
    - destruct b; firstorder congruence.
  Qed.

  Lemma run_correct p b :
    Run p b <-> exists n, run p n = Some (if b then 0 else 1).
  Proof.
    induction p in b |- *.
    - rewrite run_seq_rw. setoid_rewrite H. setoid_rewrite IHp. cbn.
      split.
      + intros (b' & (n1 & H1) & (n2 & H2)).
        exists (n1 + n2). erewrite run_mono; eauto. 2: lia.
        destruct b'.
        * eapply run_mono; eauto. lia.
        * eapply run_mono; eauto. lia.
      + intros (n & Hn). destruct (run p n) as [ [] | ] eqn:E; try congruence.
        * exists true. eauto.
        * exists false.
          eapply run_typed in E as Hle.
          destruct Hle; try lia. rewrite H0 in *.
          eauto.
    - rewrite run_call_rw. cbn. unfold Exec. split.
      + intros He.
        edestruct equiv_eva as [n Hn]. eapply He.
        destruct He as [He _].
        rewrite <- He. reflexivity.
        exists n. rewrite Hn.
        destruct b; cbv; try reflexivity.
      + intros [n Hn]. destruct eva eqn:E; try congruence.
        destruct (eqb_spec t (enc 0)), b; subst; try now firstorder congruence.
        * rewrite eva_equiv. 2: eauto. eapply eval_refl. eapply eva_lam. eauto.
        * destruct (eqb_spec t (enc 1)); subst; try now firstorder congruence.
        * destruct (eqb_spec t (enc 1)); subst; try now firstorder congruence.
          rewrite eva_equiv. 2: eauto. eapply eval_refl. eapply eva_lam. eauto.
    - rewrite run_ret_rw. cbn. split.
      + intros ->. exists 0. reflexivity.
      + intros []. destruct b0, b; congruence.
  Qed.

  Lemma closure_of' :
    forall f : input -> prog,
    exists c, forall i b, Run (f i) b <-> Exec c i b.
  Proof.
    assert EPF_L by apply CT_L_to_EPF_L, ct.
    intros f.
    unshelve epose (f' := fun i => @partial.implementation.Build_part _ (run (f i)
                                                                    ) _).
    {
      intros ? ? ? ? ?. eapply run_mono; eauto.
    }
    destruct (H f') as [c Hc].
    destruct (enum_closed c) eqn:E.
    + unshelve eexists. unshelve eexists. exact t. now eapply enum_closed_proc.
      intros i b.
      rewrite run_correct.
      unfold Exec. cbn. unfold f' in Hc. cbn in Hc.
      unfold partial.equiv in Hc.
      cbn in Hc.
      unfold partial.implementation.hasvalue in Hc.
      cbn in *.

      split.
      * rewrite <- Hc.
        intros [n Hn]. unfold T_L in Hn.
        rewrite E in Hn.
        destruct eva eqn:Heva; try congruence.
        eapply unenc_correct2 in Hn as <-.
        destruct b.
        -- erewrite eva_equiv. 2: eauto.
           eapply eval_refl. Lproc. 
        -- erewrite eva_equiv. 2: eauto.
           eapply eval_refl. Lproc. 
      * intros Hv.
        rewrite <- Hc.
        unfold T_L. rewrite E.
        edestruct equiv_eva as [n Hn]. eapply Hv.
        destruct Hv as [Hv ?].
        rewrite <- Hv. reflexivity.
        exists n. setoid_rewrite Hn.
        rewrite unenc_correct. reflexivity.
    + unshelve eexists. exists (lam Omega). Lproc.
      intros i b.
      rewrite run_correct.
      unfold Exec. cbn. unfold f' in Hc. cbn in Hc.
      unfold partial.equiv in Hc.
      cbn in Hc.
      unfold partial.implementation.hasvalue in Hc.
      cbn in *.
      intros.
      rewrite <- Hc. split.
      * intros [n Hn]. unfold T_L in Hn. rewrite E in Hn. congruence.
      * intros ?. exfalso.
        assert ((lam Omega) (enc i) ≻ Omega). eapply step_beta. now rewrite Omega_closed.
        Lproc. rewrite H1 in H0.
        destruct H0 as [H0 _].
        destruct b.
        - eapply Omega_diverges. rewrite H0. cbv. reflexivity.
        - eapply Omega_diverges. rewrite H0. cbv. reflexivity.
  Qed.

  Lemma closure_of :
    forall f : input -> input -> prog,
    exists c, ClosureOf f c.
  Proof.
    intros p. 

    (* this will work *)
  Admitted.

  Lemma closure_of_run_rw {p} {f}:
    ClosureOf f p ->
    forall j i b, Run (Call (p j) i) b <-> Run (f j i) b.
  Proof.
    unfold ClosureOf.
    intuition.
    - apply H.
      inversion_clear H0.
      assumption.
    - constructor.
      apply H.
      assumption.
  Qed.

  Definition CodeOf (f:input -> prog) (m:machine) :=
    forall (i:input) b, Run (f i) b <-> Exec m i b.

  Lemma code_of_run_rw {p} {f}:
    CodeOf f p ->
    forall i b, Run (Call p i) b <-> Run (f i) b.
  Proof.
    unfold CodeOf.
    intuition.
    - inversion_clear H0.
      apply H.
      assumption.
    - constructor.
      apply H.
      assumption.
  Qed.

  Lemma code_of :
    forall f : input -> prog,
    exists m, CodeOf f m.
  Proof.
    intros.
    destruct (closure_of (fun x => f)) as (c, hc).
    exists (c input_inhabited).
    unfold CodeOf.
    unfold ClosureOf in *.
    intros.
    rewrite hc.
    reflexivity.
  Qed.

  (*----------------------------------------------------------------------------*)

  Section RunLoopHalt.

    Lemma run_fun:
      forall p b1,
      Run p b1 ->
      forall b2,
      Run p b2 ->
      b1 = b2.
    Proof.
      intros p r1 H; induction H; intros r' He;
        inversion He; subst; clear He; auto;
        (* In each case we have a bunch of Run's that are solved
           by induction; we need to make sure we clear any dec's,
           so that we can advance to the next IH *) 
        repeat match goal with
        | [ H1: Run ?q ?b1, H2: Run ?q ?b2 |- _] =>
          (
            assert (b1 = b2) by eauto ||
            assert (b2 = b1) by eauto
          ); subst; clear H2; auto
        end;
        auto.
      eauto using exec_fun.
    Qed.

    Lemma halt_to_run:
      forall p,
      Halt p ->
      exists b, Run p b.
    Proof.
      intros.
      induction H; try destruct IHHalt as (b, Hr).
      - exists b.
        constructor.
      - exists b.
        constructor.
        assumption.
      - destruct IHHalt as (b1, Hr).
        exists b1.
        econstructor; eauto.
    Qed.

    Lemma run_to_halt:
      forall p b,
      Run p b ->
      Halt p.
    Proof.
      intros.
      induction H.
      - constructor.
      - eapply halt_call; eauto.
      - eapply halt_seq; eauto.
    Qed.

    Lemma halt_rw:
      forall p,
      Halt p <-> exists b, Run p b.
    Proof.
      split; intros.
      - auto using halt_to_run.
      - destruct H.
        eauto using run_to_halt.
    Qed.

    Lemma code_of_halt_rw {p} {f}:
      CodeOf f p ->
      forall i, Halt (Call p i) <-> Halt (f i).
    Proof.
      intros.
      repeat rewrite halt_rw.
      split; intros (x, Hx); exists x.
      - rewrite (code_of_run_rw H) in Hx.
        assumption.
      - rewrite (code_of_run_rw H).
        assumption.
    Qed.


    Lemma closure_of_halt_rw {p} {f}:
      ClosureOf f p ->
      forall j i, Halt (Call (p j) i) <-> Halt (f j i).
    Proof.
      intros.
      repeat rewrite halt_rw.
      split; intros (x, Hx); exists x.
      - rewrite (closure_of_run_rw H) in Hx.
        assumption.
      - rewrite (closure_of_run_rw H).
        assumption.
    Qed.

    Lemma halt_or_loop:
      forall p,
      Halt p \/ Loop p.
    Proof.
      induction p; intros.
      - destruct IHp as [IH|IH].
        + apply halt_to_run in IH.
          destruct IH as (b, IH).
          assert (H := H b).
          destruct H as [H|H]. {
            left.
            econstructor; eauto.
          }
          right.
          eapply loop_seq_r; eauto.
        + right.
          eauto using loop_seq_l.
      - destruct (exec_exists m i) as [(b, He)|Hl]. {
          left.
          econstructor.
          eauto.
        }
        right.
        constructor.
        auto.
      - left.
        constructor.
    Qed.

    Lemma loop_to_not_halt:
      forall p,
      Loop p ->
      ~ Halt p.
    Proof.
      intros; induction H; intros N; inversion_clear N;
        try (contradict IHLoop; auto; fail).
      - apply H in H0.
        assumption.
      - contradict IHLoop.
        eapply run_to_halt; eauto.
      - assert (b0 = b) by eauto using run_fun.
        subst.
        contradiction.
    Qed.

    Lemma halt_to_not_loop:
      forall p,
      Halt p ->
      ~ Loop p.
    Proof.
      intros.
      induction H; intros N.
      - inversion_clear N.
      - inversion_clear N.
        contradict H.
        auto.
      - inversion_clear N. {
          apply loop_to_not_halt in H1.
          contradict H1.
          eapply run_to_halt; eauto.
        }
        assert (b0 = b) by eauto using run_fun.
        subst.
        contradiction.
    Qed.

    Lemma not_halt_to_loop:
      forall p,
      ~ Halt p ->
      Loop p.
    Proof.
      intros.
      destruct (halt_or_loop p). {
        contradiction.
      }
      assumption.
    Qed.

    Lemma loop_rw:
      forall p,
      Loop p <-> ~ Halt p.
    Proof.
      split; intros. {
        auto using loop_to_not_halt.
      }
      auto using not_halt_to_loop.
    Qed.

    Lemma code_of_loop_rw {p} {f}:
      CodeOf f p ->
      forall i, Loop (Call p i) <-> Loop (f i).
    Proof.
      intros.
      repeat rewrite loop_rw.
      repeat rewrite (code_of_halt_rw H).
      reflexivity.
    Qed.

    Lemma closure_of_loop_rw {p} {f}:
      ClosureOf f p ->
      forall j i, Loop (Call (p j) i) <-> Loop (f j i).
    Proof.
      intros.
      repeat rewrite loop_rw.
      rewrite (closure_of_halt_rw H).
      reflexivity.
    Qed.

    Lemma run_exists:
      forall p,
      (exists b, Run p b) \/ Loop p.
    Proof.
      intros.
      destruct (halt_or_loop p); auto.
      rewrite halt_rw in *.
      auto.
    Qed.

    Lemma loop_alt_rw:
      forall p,
      Loop p <-> (forall b, ~ Run p b).
    Proof.
      split; intros. {
        rewrite loop_rw in H.
        intros N.
        contradict H.
        eauto using run_to_halt.
      }
      rewrite loop_rw.
      intros N.
      rewrite halt_rw in N.
      destruct N as (b, N).
      apply H in N.
      contradiction.
    Qed.

    Lemma negative_alt_rw:
      forall p,
      Negative p <-> (Run p false \/ Loop p).
    Proof.
      split; intros. { inversion_clear H; auto. }
      destruct H. { auto using negative_run_false. }
      auto using negative_loop.
    Qed.

    Lemma negative_rw:
      forall p,
      Negative p <-> ~ Run p true.
    Proof.
      split; intros. {
        intros N.
        inversion_clear H. {
          assert (X: true = false) by eauto using run_fun.
          inversion X.
        }
        rewrite loop_rw in *.
        contradict H0.
        eapply run_to_halt; eauto.
      }
      destruct (halt_or_loop p). {
        rewrite halt_rw in *.
        destruct H0 as ([], Ha); try contradiction.
        auto using negative_run_false.
      }
      auto using negative_loop.
    Qed.

    Lemma code_of_negative_rw {p} {f}:
      CodeOf f p ->
      forall i, Negative (Call p i) <-> Negative (f i).
    Proof.
      intros.
      repeat rewrite negative_rw.
      repeat rewrite (code_of_run_rw H).
      reflexivity.
    Qed.

    Lemma closure_of_negative_rw {p} {f}:
      ClosureOf f p ->
      forall i j, Negative (Call (p j) i) <-> Negative (f j i).
    Proof.
      intros.
      repeat rewrite negative_rw.
      rewrite (closure_of_run_rw H).
      reflexivity.
    Qed.

    Lemma run_true_or_negative:
      forall p,
      Run p true \/ Negative p.
    Proof.
      intros.
      destruct (run_exists p) as [([], H)|H];
        auto;
        right;
        auto using negative_run_false, negative_loop.
    Qed.

    Lemma negative_ret:
      Negative (Ret false).
    Proof.
      intros.
      left.
      constructor.
    Qed.

  End RunLoopHalt.

  Local Instance extract_eqb : computable eqb.
  Proof.
    extract.
  Qed.

  Fixpoint prog_to_term (p : prog) : term.
  Proof.
    destruct p as [ p c | | ].
    - exact (prog_to_term p (lam (prog_to_term (c true))) (lam (lam (prog_to_term (c false)))) I).
    - exact (ext eqb (Eval (enc (app m (enc i)))) (enc (enc 0)) (lam (enc 0)) (lam (ext eqb (Eval (enc (app m (enc i)))) (enc (enc 1)) (lam (enc 1)) (lam Omega) I)) I).
    - exact (enc (if b then 0 else 1)).
  Defined.

  Lemma prog_to_term_closed p :
    closed (prog_to_term p).
  Proof.
    induction p; cbn.
    - Lproc.
    - unfold Eval. Lproc.
    - unfold Eval. Lproc.
  Qed.

  Lemma closed_lam t : closed t -> closed (lam t).
  Proof.
    intros.
    Lproc'. Lproc'. now eapply closed_dcl_x.
  Qed.

  Lemma Omega_eval t : ~ Omega ⇓ t.
  Proof.
    intros (? & ? & ->). eapply Omega_diverges. eauto.
  Qed.

  Lemma prog_to_term_bool p :
    forall t, eval (prog_to_term p) t -> exists b : bool, t = enc (if b then 0 else 1).
  Proof.
    intros t H. induction p in t, H |- *; cbn in *.
    + assert (converges (prog_to_term p (lam (prog_to_term (p0 true))) (lam (lam (prog_to_term (p0 false)))) I)) as [[[[t' C] % eval_converges _] % app_converges _] % app_converges _] % app_converges by now eapply Seval.eval_converges.
      eapply IHp in C as C'.
      destruct C' as [b0 ->].
      destruct b0.
      * eapply H0. rewrite C in H.
        eapply equiv_eval_proper. 3: exact H. 2: reflexivity. clear.
         unfold enc at 1. cbn.
         set (a := (lam (prog_to_term (p0 true)))) in *.
         assert (proc a). { split. 2: subst a; eauto. subst a. eapply closed_lam, prog_to_term_closed. }
         set (c := (lam (prog_to_term (p0 false)))).
         assert (proc c). { subst c. split. 2: eauto. eapply closed_lam, prog_to_term_closed. }
         Lsimpl.
         subst a.
         assert (closed (prog_to_term (p0 true))) by eapply prog_to_term_closed.
         econstructor.
         eapply step_beta. rewrite subst_closed. reflexivity. eapply prog_to_term_closed. Lproc.
      * eapply H0. rewrite C in H.
        eapply equiv_eval_proper. 3: exact H. 2: reflexivity. clear.
         unfold enc at 1. cbn.
         set (a := (lam (prog_to_term (p0 true)))) in *.
         assert (proc a). { split. 2: subst a; eauto. subst a. eapply closed_lam, prog_to_term_closed. }
         set (c := (lam (prog_to_term (p0 false)))).
         assert (proc c). { subst c. split. 2: eauto. eapply closed_lam, prog_to_term_closed. }
         Lsimpl.
         subst a.
         assert (closed (prog_to_term (p0 true))) by eapply prog_to_term_closed.
         econstructor.
         eapply step_beta. rewrite subst_closed. reflexivity. eapply prog_to_term_closed. Lproc.
    + eapply Seval.eval_converges in H as C.
      eapply app_converges in C as [C _].
      eapply app_converges in C as [C _].
      eapply app_converges in C as [C _].
      eapply app_converges in C as [C _].
      eapply app_converges in C as [_ C].
      eapply Eval_converges in C as [t' [C L]].
      assert (Eval (enc (m (enc i))) == enc t') as E. {
        change (enc (m (enc i))) with (ext (m (enc i))).
        destruct L as [? ->].
        rewrite eval_Eval. 2: now eapply eproc_equiv.
        reflexivity.
      }
      rewrite E in H at 1.
      assert (ext eqb (enc t') (enc (enc 0)) == enc (eqb t' (enc 0))) as E' by now Lsimpl.
      rewrite E' in H.
      destruct (eqb_spec t' (enc 0)).
      * exists true. subst. eapply eval_unique. eauto. clear H.
        unfold Eval. Lsimpl. eapply eval_refl. Lproc.
      * destruct (eqb_spec t' (enc 1)).
        exists false. subst. eapply eval_unique. eauto. clear H.
        unfold Eval. Lsimpl.
        fold Eval.
        eapply eval_helper. econstructor 2.
        eapply step_beta. rewrite subst_closed. reflexivity. unfold Eval. Lproc. Lproc.
        econstructor.
        rewrite E.
        Lsimpl.
        change (eqb (enc 1) (enc 1)) with true. cbn. Lsimpl. eapply eval_refl. Lproc.
        exfalso.
        eapply Omega_eval.
        eapply equiv_eval_proper. 3: exact H. 2: reflexivity. clear H.
        unfold Eval. Lsimpl. fold Eval.
        etransitivity. econstructor.
        eapply step_beta. rewrite subst_closed. reflexivity. unfold Eval. Lproc. Lproc.
        rewrite E. Lsimpl.
        destruct (eqb_spec t' (enc 1)); try congruence.
        econstructor.
        eapply step_beta. rewrite subst_closed. reflexivity. Lproc. Lproc.
    + exists b. eapply eval_unique. eauto. eapply eval_refl. Lproc.
  Qed.

  Lemma prog_to_term_correct p b :
    Run p b <-> eval (prog_to_term p) (enc (if b then 0 else 1)).
  Proof.
    induction p in b |- *; cbn.
    - rewrite run_seq_rw.
      setoid_rewrite IHp.
      setoid_rewrite H.
      split.
      {
        intros (b' & H1 & H2).
        Lsimpl.
        destruct b'.
        + unfold enc at 1. cbn.
          set (a := (lam (prog_to_term (p0 true)))) in *.
          assert (proc a). { split. 2: subst a; eauto. subst a. eapply closed_lam, prog_to_term_closed. }
          set (c := (lam (prog_to_term (p0 false)))).
          assert (proc c). { subst c. split. 2: eauto. eapply closed_lam, prog_to_term_closed. }
          Lsimpl.
          unfold a.
          assert (closed (prog_to_term (p0 true))) by eapply prog_to_term_closed.
          eapply eval_helper.
          econstructor 2. 2: econstructor.
          eapply step_beta. rewrite subst_closed. reflexivity. eapply prog_to_term_closed. Lproc.
          eauto.
        + unfold enc at 1. cbn.
          set (a := (lam (prog_to_term (p0 true)))) in *.
          assert (proc a). { split. 2: subst a; eauto. subst a. eapply closed_lam, prog_to_term_closed. }
          set (c := (lam (prog_to_term (p0 false)))).
          assert (proc c). { subst c. split. 2: eauto. eapply closed_lam, prog_to_term_closed. }
          Lsimpl.
          unfold c.
          assert (closed (prog_to_term (p0 false))) by eapply prog_to_term_closed.
          eapply eval_helper.
          econstructor 2. 2: econstructor.
          eapply step_beta. rewrite subst_closed. reflexivity. eapply prog_to_term_closed. Lproc.
          eauto.
      }
      intros.
      assert (converges (prog_to_term p (lam (prog_to_term (p0 true))) (lam (lam (prog_to_term (p0 false)))) I)) as [[[[t' C] % eval_converges _] % app_converges _] % app_converges _] % app_converges by now eapply Seval.eval_converges.
      eapply prog_to_term_bool in C as C'.
      destruct C' as [b0 ->].
      exists b0. split. eauto.
      destruct b0.
      * rewrite C in H0 at 1.
        eapply equiv_eval_proper. 2: reflexivity. 2: exact H0. clear H0.
        set (a := (lam (prog_to_term (p0 true)))) in *.
        assert (proc a). { split. 2: subst a; eauto. subst a. eapply closed_lam, prog_to_term_closed. }
        set (c := (lam (prog_to_term (p0 false)))).
        assert (proc c). { subst c. split. 2: eauto. eapply closed_lam, prog_to_term_closed. }
        Lsimpl.
        subst a.
        assert (closed (prog_to_term (p0 true))) by eapply prog_to_term_closed.
        econstructor.
        eapply step_beta. rewrite subst_closed. reflexivity. eapply prog_to_term_closed. Lproc.
      * rewrite C in H0 at 1.
        eapply equiv_eval_proper. 2: reflexivity. 2: exact H0. clear H0.
        set (a := (lam (prog_to_term (p0 true)))) in *.
        assert (proc a). { split. 2: subst a; eauto. subst a. eapply closed_lam, prog_to_term_closed. }
        set (c := (lam (prog_to_term (p0 false)))).
        assert (proc c). { subst c. split. 2: eauto. eapply closed_lam, prog_to_term_closed. }
        Lsimpl.
        subst c.
        assert (closed (prog_to_term (p0 true))) by eapply prog_to_term_closed.
        econstructor.
        eapply step_beta. rewrite subst_closed. reflexivity. eapply prog_to_term_closed. Lproc.
    - rewrite run_call_rw. unfold Exec.
      split.
      + intros H.
        change (enc (m (enc i))) with (ext (m (enc i))).
        rewrite eval_Eval at 1; eauto.
        Lsimpl.
        destruct b.
        * change (eqb (enc 0) (enc 0)) with true.
          rewrite bool_enc_correct. 2: Lproc. 2:{ destruct m. cbn. unfold Eval. Lproc. }
          Lsimpl. eapply eval_refl. Lproc.
        * change (eqb (enc 1) (enc 0)) with false.
          destruct m as [m Hcl].
          rewrite bool_enc_correct. 2: Lproc. 2:{ unfold Eval. Lproc. }
          eapply eval_helper.
          econstructor 2. 2: econstructor.
          eapply step_beta. rewrite subst_closed. 2: { cbn. unfold Eval. Lproc. } 2: Lproc.
          reflexivity.
          cbn in *.
          rewrite eval_Eval; eauto.
          Lsimpl.
          change (eqb (enc 1) (enc 1)) with true.
          cbn. Lsimpl. eapply eval_refl. Lproc.
      +  intros H. eapply Seval.eval_converges in H as C.
         eapply app_converges in C as [C _].
         eapply app_converges in C as [C _].
         eapply app_converges in C as [C _].
         eapply app_converges in C as [C _].
         eapply app_converges in C as [_ C].
         eapply Eval_converges in C as [t' [C L]].
         assert (Eval (enc (m (enc i))) == enc t') as E. {
           change (enc (m (enc i))) with (ext (m (enc i))).
           destruct L as [? ->].
           rewrite eval_Eval. 2: now eapply eproc_equiv.
           reflexivity.
         }
         rewrite E in H at 1.
         assert (ext eqb (enc t') (enc (enc 0)) == enc (eqb t' (enc 0))) as E' by now Lsimpl.
         rewrite E' in H. clear E'.

         destruct (eqb_spec t' (enc 0)).
         * subst. eapply equiv_eval_proper in H.
           2:{ clear H. unfold Eval. Lsimpl. reflexivity. }
           2: reflexivity.
           rewrite C.
           eauto.
         * eapply equiv_eval_proper in H.
           2:{ clear H. unfold Eval. Lsimpl.
               etransitivity. econstructor.
               eapply step_beta. rewrite subst_closed. reflexivity.
               Lproc. Lproc. fold Eval.
               rewrite E. Lsimpl.
               reflexivity.
           } 2: reflexivity.
           destruct (eqb_spec t' (enc 1)).
           -- subst.
              assert (lam (enc 1) (lam # 0) == enc 1). { cbv. now Lsimpl. }
              rewrite H0 in H. now rewrite C.
           -- edestruct Omega_eval.
              assert (lam Omega (lam # 0) == Omega). {
                econstructor. eapply step_beta. rewrite subst_closed. reflexivity.
               Lproc. Lproc.
              }
              rewrite H0 in H. eauto.
    - rewrite run_ret_rw. split.
      + intros ->. apply eval_refl. apply proc_enc.
      + intros ?.
        enough ((if b0 then 0 else 1) = (if b then 0 else 1)) by (destruct b0, b; congruence).
        eapply nat_enc_inj.
        eapply eval_unique. 2: eassumption.
        apply eval_refl, proc_enc.
  Qed.

  Definition compile : prog -> machine.
    intros p. unshelve eexists.
    exact (lam (prog_to_term p)).
    abstract eapply closed_lam, prog_to_term_closed.
  Defined.

  Lemma compile_run_rw :
    forall i p b,
    Run (Call (compile p) i) b <-> Run p b.
  Proof.
    intros i p b. rewrite run_call_rw.
    unfold Exec, compile.
    cbn.
    assert (lam (prog_to_term p) (enc i) == prog_to_term p) as E.
    { econstructor. eapply step_beta.
      2: Lproc. rewrite subst_closed. reflexivity. eapply prog_to_term_closed.
    }
    rewrite prog_to_term_correct.
    split.
    - intros H. now rewrite <- E.
    - intros H. now rewrite E.
  Qed.

  (** We also define a function to serialize a machine into a string (of type
      input). In the book, this corresponds to notation <M>. *)
  Parameter encode_mach: machine -> input.
  (** Similarly, we have a function that takes a string and produces a machine.
      In the book, this corresponds to notation M = <M> *)
  Parameter decode_mach: input -> machine.
  (** Decoding and encoding a machine yields the same machine. *)
  Axiom decode_encode_mach_rw:
    forall m,
    decode_mach (encode_mach m) = m.
  Axiom encode_decode_mach_rw:
    forall w, encode_mach (decode_mach w) = w.

  (** Given a machine and a string, encodes the pair as a string.
      In the book, this corresponds to notation <M, w>. *)
  Definition encode_mach_input (M:machine) (w:input) : input :=
    encode_pair (encode_mach M, w).

  (** Given a string this function deserializes a pair M and w, given an encoded
      string <M,w>. *)
  Definition decode_mach_input p := let (M, w) :=
    decode_pair p in (decode_mach M, w).

  (** Decoding and encoding a pair yields the same pair. *)
  Lemma decode_encode_mach_input_rw:
    forall M w,
    decode_mach_input
          (encode_mach_input M w) = (M, w).
  Proof.
    intros.
    unfold decode_mach_input.
    unfold encode_mach_input.
    rewrite decode_encode_pair_rw.
    rewrite decode_encode_mach_rw.
    reflexivity.
  Qed.

  (** Let us define an abbreviation of the above functions. *)
  Notation "'<<' w1 ',' w2 '>>'" := (encode_pair w1 w2).
  Notation "'[[' M ']]'" := (encode_mach M).
  Notation "'<[' M , w ']>'" := (encode_mach_input M w).


  Section Examples.
    Let a_tm_1 (s:input -> prog) : input -> prog :=
    fun i =>
      mlet b <- s <[ decode_mach i, i ]> in
      if b then Ret false
           else Ret true
    .
    Let a_tm_2 := fun p => 
      let (M, w) := decode_mach_input p in
      Call M w.

    Let halt_tm (s:input -> prog) := fun p =>
        let (M, w) := decode_mach_input p in
        mlet b <- s p in
        if b then Call M w else Ret false.

    Let e_tm_1 p x := let (M, w) := decode_mach_input p in
          if input_eq_dec x w then (
            Call M w
          ) else Ret false
        .

    Let e_tm_2 s (inner:input -> machine) := fun p =>
        let (M, w) := decode_mach_input p in
        mlet b <- s [[ inner p ]] in
        if b then Ret false else Ret true.
  End Examples.


  (** Define the equivalence of languages *)
  Definition Equiv (L1 L2:lang) :=
    forall i,
    L1 i <-> L2 i.

  Definition Impl (L1 L2:lang) := 
    forall w,
    L1 w -> L2 w.

  Notation "A ≡ B" := (Equiv A B) (at level 80, right associativity).

  (** We use a direct definition of recognition:
      The turing machine accepts input i (with `run m i`)
      iff language L accepts i.
       *)

  Definition Recognizes (p: input -> prog) (L:lang) :=
    forall i, Run (p i) true <-> L i.

  Lemma recognizes_def {p} {L}:
    (forall i, Run (p i) true <-> L i) ->
    Recognizes p L.
  Proof.
    intros.
    unfold Recognizes.
    assumption.
  Qed.

  Lemma recognizes_rw {p} {L}:
    Recognizes p L ->
    forall i, Run (p i) true <-> L i.
  Proof.
    unfold Recognizes.
    intuition.
  Qed.

  Lemma recognizes_def_2:
    forall p (L:lang),
    (forall i, Run (p i) true -> L i) ->
    (forall i, L i -> Run (p i) true) ->
    Recognizes p L.
  Proof.
    intros.
    unfold Recognizes.
    intros; split; auto.
  Qed.

  Lemma recognizes_impl:
    forall p L1 L2,
    Equiv L1 L2 ->
    Recognizes p L1 ->
    Recognizes p L2.
  Proof.
    intros.
    unfold Recognizes in *.
    intros.
    rewrite H0.
    apply H.
  Qed.

  Lemma equiv_symm:
    forall L1 L2,
    Equiv L1 L2 <-> Equiv L2 L1.
  Proof.
    unfold Equiv; split; intros.
    - rewrite H.
      intuition.
    - rewrite H.
      intuition.
  Qed.

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

  Lemma equiv_sym:
    forall L1 L2,
    Equiv L1 L2 ->
    Equiv L2 L1.
  Proof.
    unfold Equiv; split; intros; apply H; assumption.
  Qed.

  (** Register [Equiv] in Coq's tactics. *)
  Global Add Parametric Relation : lang Equiv
    reflexivity proved by equiv_refl
    symmetry proved by equiv_sym
    transitivity proved by equiv_trans
    as l_equiv_setoid.

  Import Morphisms.

  Global Instance recognizes_equiv_proper: Proper (eq ==> Equiv ==> iff) Recognizes.
  Proof.
    unfold Proper, respectful, Equiv, Recognizes.
    intros.
    split; intros; split; intros; subst;
    try (apply H0; apply H1; auto);
    try (apply H1; apply H0; auto).
  Qed.


  (** A language is recognizable, that is
      there is some machine m that recognizes it. *)

  Definition Recognizable (L:lang) : Prop :=
    exists p, Recognizes p L.

  Global Instance recognizable_equiv_proper: Proper (Equiv ==> iff) Recognizable.
  Proof.
    unfold Proper, respectful, Recognizable.
    intros.
    split; intros (p, Hx).
    - rewrite H in Hx.
      eauto.
    - rewrite <- H in Hx.
      eauto.
  Qed.

  Lemma recognizable_def:
    forall p L, Recognizes p L -> Recognizable L.
  Proof.
    intros.
    exists p.
    assumption.
  Qed.

  Section RecognizesRun.

    Lemma recognizes_run_false_to_not_in:
      forall p L i,
      Recognizes p L ->
      Run (p i) false ->
      ~ L i.
    Proof.
      intros.
      intros N.
      apply H in N.
      assert (Hx: true = false) by eauto using run_fun.
      inversion Hx.
    Qed.

    Lemma recognizes_run_true_to_in:
      forall p L,
      Recognizes p L ->
      forall i,
      Run (p i) true ->
      L i.
    Proof.
      intros.
      apply H.
      assumption.
    Qed.

    Lemma recognizes_not_in_to_not_run_true:
      forall p L,
      Recognizes p L ->
      forall i,
      ~ L i ->
      ~ Run (p i) true.
    Proof.
      intros.
      intros N.
      assert (L i). { eapply recognizes_run_true_to_in; eauto. }
      contradiction.
    Qed.

    Lemma recognizes_not_in_to_negative:
      forall p L,
      Recognizes p L ->
      forall i,
      ~ L i ->
      Negative (p i).
    Proof.
      intros.
      rewrite negative_rw.
      eauto using recognizes_not_in_to_not_run_true.
    Qed.

    Lemma recognizes_in_to_run_true:
      forall p L i,
      Recognizes p L ->
      L i ->
      Run (p i) true.
    Proof.
      intros.
      apply H in H0.
      assumption.
    Qed.

    Lemma recognizes_loop_to_not_in:
      forall p L,
      Recognizes p L ->
      forall i,
      Loop (p i) ->
      ~ L i.
    Proof.
      intros.
      intros N.
      apply H in N.
      apply halt_to_not_loop in H0; auto.
      eauto using run_to_halt.
    Qed.

    Lemma recognizes_negative_to_not_in:
      forall p L,
      Recognizes p L ->
      forall i,
      Negative (p i) ->
      ~ L i.
    Proof.
      intros.
      inversion_clear H0.
      - eauto using recognizes_run_false_to_not_in.
      - eauto using recognizes_loop_to_not_in.
    Qed.

    Lemma recognizes_accept_rw {p} {L}:
      Recognizes p L ->
      forall i,
      Run (p i) true <-> L i.
    Proof.
      unfold Recognizes.
      auto.
    Qed.

    Lemma lang_equiv:
      forall L1 L2,
      Equiv L1 L2 ->
      forall m,
      Recognizes m L1 <-> Recognizes m L2.
    Proof.
      split; unfold Recognizes; intros.
      - rewrite H0.
        auto.
      - rewrite H0.
        symmetry.
        auto.
    Qed.

  End RecognizesRun.

  (*----------------------------------------------------------------------------*)

  Section Complement.
    Definition compl L : lang := fun i => not (L i).

    Lemma co_co_rw:
      forall L,
      Equiv (compl (compl L)) L.
    Proof.
      intros.
      unfold Equiv.
      split; intros. {
        destruct (Classical_Prop.classic (L i)). {
          assumption.
        }
        apply H in H0.
        inversion H0.
      }
      unfold compl.
      intros N.
      contradiction.
    Qed.

    Lemma co_recognizes_run_true_to_not_in:
      forall p L i,
      Recognizes p (compl L) ->
      Run (p i) true ->
      ~ L i.
    Proof.
      intros.
      apply recognizes_run_true_to_in with (L:=compl L) in H0; auto.
    Qed.

    Lemma co_recognizes_in_to_not_run_true:
      forall p L i,
      Recognizes p (compl L) ->
      L i ->
      ~ Run (p i) true.
    Proof.
      intros.
      intros N.
      apply H in N.
      contradiction.
    Qed.

    Lemma co_recognizes_not_in_to_run_true:
      forall p L i,
      Recognizes p (compl L) ->
      ~ L i ->
      Run (p i) true.
    Proof.
      intros.
      unfold compl in *.
      apply H in H0.
      assumption.
    Qed.

  End Complement.

  (*----------------------------------------------------------------------------*)

  Section Decidable.
    (** We define a decider as any Turing Machine that returns either Accept or
        Reject, but not Loop. *)

    Definition Decider (p:input -> prog) := forall i, Halt (p i).

    Lemma decider_def:
      forall p,
      (forall i, Halt (p i)) ->
      Decider p.
    Proof.
      intros.
      unfold Decider; intros. eauto.
    Qed.

    Definition Decides p L := Recognizes p L /\ Decider p.

    Lemma decides_def:
      forall p L,
      Recognizes p L ->
      Decider p ->
      Decides p L.
    Proof.
      intros.
      split; assumption.
    Qed.

    Definition Decidable L := exists p, Decides p L.

    Lemma decidable_def:
      forall p L, Decides p L -> Decidable L.
    Proof.
      intros.
      exists p.
      assumption.
    Qed.

    Lemma decidable_to_recognizable:
      forall L,
      Decidable L ->
      Recognizable L.
    Proof.
      intros.
      destruct H as (p, H).
      destruct H.
      apply recognizable_def with (p:=p).
      assumption.
    Qed.

    Lemma unrecognizable_to_undecidable:
      forall L,
       ~ Recognizable L ->
       ~ Decidable L.
    Proof.
      intros.
      intros N.
      apply decidable_to_recognizable in N.
      contradiction.
    Qed.

    Lemma decides_to_recognizes:
      forall m L,
      Decides m L ->
      Recognizes m L.
    Proof.
      intros.
      destruct H.
      assumption.
    Qed.

    Lemma decides_run_false_to_not_in:
      forall p L i,
      Decides p L ->
      Run (p i) false ->
      ~ L i.
    Proof.
      intros.
      apply decides_to_recognizes in H.
      apply recognizes_run_false_to_not_in with (p:=p); auto.
    Qed.

    Lemma decides_run_true_to_in:
      forall p L i,
      Decides p L ->
      Run (p i) true ->
      L i.
    Proof.
      intros.
      apply decides_to_recognizes in H.
      apply recognizes_run_true_to_in with (p:=p); auto.
    Qed.

    Lemma decides_in_to_run_true:
      forall p L i,
      Decides p L ->
      L i ->
      Run (p i) true.
    Proof.
      intros.
      apply decides_to_recognizes in H.
      apply recognizes_in_to_run_true with (L:=L); auto.
    Qed.

    Lemma decider_to_halt:
      forall p,
      Decider p ->
      forall i,
      Halt (p i).
    Proof.
      intros.
      unfold Decider in *.
      auto.
    Qed.

    Lemma decider_to_run:
      forall p i,
      Decider p ->
      exists b, Run (p i) b.
    Proof.
      intros.
      apply decider_to_halt with (i:=i) in H.
      rewrite halt_rw in *.
      assumption.
    Qed.

    Lemma decides_to_run:
      forall p L i,
      Decides p L ->
      exists b, Run (p i) b.
    Proof.
      intros.
      destruct H.
      specialize (H0 i).
      rewrite halt_rw in *.
      assumption.
    Qed.

    Lemma decides_to_halt:
      forall p L,
      Decides p L ->
      forall i,
      Halt (p i).
    Proof.
      intros.
      destruct H.
      unfold Decider in *.
      auto.
    Qed.

    Lemma decider_to_not_loop:
      forall p,
      Decider p ->
      forall i,
      ~ Loop (p i).
    Proof.
      intros.
      specialize (H i).
      auto using halt_to_not_loop.
    Qed.

    Lemma decider_not_run_false_to_run_true:
      forall p i,
      Decider p ->
      ~ Run (p i) false ->
      Run (p i) true.
    Proof.
      intros.
      assert (H := H i).
      rewrite halt_rw in *.
      destruct H as (b, H).
      destruct b;
      intuition.
    Qed.

    Lemma decider_not_run_true_to_run_false:
      forall p i,
      Decider p ->
      ~ Run (p i) true ->
      Run (p i) false.
    Proof.
      intros.
      assert (H := H i).
      rewrite halt_rw in *.
      destruct H as (b, H).
      destruct b;
      intuition.
    Qed.

    Lemma decides_to_decider:
      forall p L,
      Decides p L ->
      Decider p.
    Proof.
      intros.
      unfold Decides in *.
      destruct H; assumption.
    Qed.

    Lemma decides_or :
      forall p P, Decides p P -> forall i, P i \/ ~ P i. 
    Proof.
      intros.
      destruct decides_to_run with (i:= i) (p:= p) (L:= P) as ([], Ha); auto.
      - left.
        apply decides_run_true_to_in with (p:= p); auto.
      - right.
          apply decides_run_false_to_not_in with (p:= p); auto.
    Qed.

    Lemma decides_not_in_to_run_false:
      forall p L i,
      Decides p L ->
      ~ L i ->
      Run (p i) false.
    Proof.
      intros.
      destruct H.
      assert (Ha: Halt (p i)) by auto using decider_to_halt.
      rewrite halt_rw in *.
      destruct Ha as (b, Ha).
      destruct b; auto.
      contradict H0.
      eapply recognizes_run_true_to_in; eauto.
    Qed.

    Lemma run_seq_pre_rw {p} {b'}:
      Run p b' ->
      forall q b ,
      Run (Seq p q) b <-> Run (q b') b.
    Proof.
      intros.
      rewrite run_seq_rw.
      split; intros. {
        destruct H0 as (b1, (Hr1, Hr2)).
        assert (b' = b1) by eauto using run_fun.
        subst.
        assumption.
      }
      exists b'.
      intuition.
    Qed.

    Lemma decides_false_rw:
      forall f P,
      Decides f P ->
      forall i,
      Run (f i) false <-> ~ P i.
    Proof.
      split; intros. {
        eauto using decides_run_false_to_not_in.
      }
      eauto using decides_not_in_to_run_false.
    Qed.

    Lemma decides_true_rw {f} {P}:
      Decides f P ->
      forall i,
      Run (f i) true <-> P i.
    Proof.
      split; intros. {
        eapply decides_run_true_to_in; eauto.
      }
      eauto using decides_in_to_run_true.
    Qed.

    Lemma halt_seq_alt:
      forall p (c:bool -> prog),
      Halt p ->
      (forall (b:bool), Run p b -> Halt (c b)) -> 
      Halt (Seq p c).
    Proof.
      intros.
      rewrite halt_rw in H.
      destruct H as (b, H).
      apply halt_seq with (b:=b); auto.
    Qed.

    Lemma halt_seq_decider:
      forall p j (c:bool -> prog),
      Decider p ->
      (forall (b:bool), Run (p j) b -> Halt (c b)) -> 
      Halt (Seq (p j) c).
    Proof.
      intros.
      apply halt_seq_alt. {
        apply H.
      }
      intros.
      apply H0.
      assumption.
    Qed.

    Lemma halt_seq_decides:
      forall p j L (c:bool -> prog),
      Decides p L ->
      (forall (b:bool), Run (p j) b -> Halt (c b)) -> 
      Halt (Seq (p j) c).
    Proof.
      intros.
      apply halt_seq_decider; auto.
      destruct H; auto.
    Qed.

  End Decidable.


  (** Tactics that simplify `Run` objects in the assumptions. *)

  Ltac run_simpl_inv :=
  match goal with
  | [ H: _ |- _ ] =>
    match type of H with
      | Run (Ret _) _ => idtac
      | Loop (Ret _) => idtac
      | Halt (Ret _) => idtac
      | _ => fail
    end;
    inversion H; subst; clear H
  end.

  Ltac run_simpl_explode :=
    match goal with
    | [ H: _ |- _ ]  =>
        match type of H with
        | true = true => idtac
        | false = false => idtac

        | false = true => idtac
        | true = false => idtac

        | False => idtac
        | _ => fail
        end; inversion H
    end.

  Ltac run_simpl_rw := (
      rewrite decode_encode_mach_input_rw in * ||
      rewrite decode_encode_pair_rw in * ||
      rewrite encode_decode_pair_rw in * ||
      rewrite decode_encode_mach_rw in * ||
      rewrite encode_decode_mach_rw in * ||
      rewrite compile_run_rw in *).


  Ltac run_simpl_norm :=
    match goal with
    | [ H: ?x = ?x |- _] => clear H
    | [ H1: Negative ?p, H2: Run ?p true |- _ ] =>
      rewrite negative_rw in H1; contradiction
    | [ H1: Run ?p _, H2: Loop ?p |- _ ] =>
      apply run_to_halt in H1;
      rewrite loop_rw in H2; contradiction

    | [ H1: CodeOf _ ?p, H2: Run (Call ?p _) _ |- _ ] => 
      rewrite (code_of_run_rw H1) in H2
    | [ H1: CodeOf _ ?p |- context[Run (Call ?p _) _] ] => 
      rewrite (code_of_run_rw H1)

    | [ H1: CodeOf _ ?p, H2: Negative (Call ?p _) |- _ ] => 
      rewrite (code_of_negative_rw H1) in H2
    | [ H1: CodeOf _ ?p |- context[Negative (Call ?p _)] ] => 
      rewrite (code_of_negative_rw H1)

    | [ H1: CodeOf _ ?p, H2: Loop (Call ?p _) |- _ ] => 
      rewrite (code_of_loop_rw H1) in H2
    | [ H1: CodeOf _ ?p |- context[Loop (Call ?p _)] ] => 
      rewrite (code_of_loop_rw H1)

    | [ H1: CodeOf _ ?p, H2: Halt (Call ?p _) |- _ ] => 
      rewrite (code_of_halt_rw H1) in H2
    | [ H1: CodeOf _ ?p |- context[Halt (Call ?p _)] ] => 
      rewrite (code_of_halt_rw H1)

    | [ H1: Halt ?p , H2: Loop ?p  |- _ ] =>
      rewrite loop_rw in H2; contradiction
    | [ H1: Run ?m ?r1, H2: Run ?m ?r2  |- _] =>
      assert (r1 = r2) by eauto using run_fun;
      subst; clear H1
    | [ H1: Exec ?m ?r1, H2: Exec ?m ?r2  |- _] =>
      assert (r1 = r2) by eauto using exec_fun;
      subst; clear H1
    | [ H: true = _ |- _ ] => symmetry in H
    | [ H: false = _ |- _ ] => symmetry in H
    | [ H: negb _ = true |- _ ] => apply negb_true_iff in H; subst
    | [ H: negb _ = false |- _ ] => apply negb_false_iff in H; subst
    | [ H: andb _ _ = true |- _] => apply andb_prop in H
    | [ H: _ /\ _ |- _ ] => destruct H
    end.

  Ltac run_simpl :=
    run_simpl_rw ||
    run_simpl_explode ||
    run_simpl_norm ||
    run_simpl_inv.


  (** Simplify everything *)

  Ltac run_simpl_all := repeat run_simpl.
