Require Coq.Classes.RelationClasses.
Require Coq.Relations.Relations.
Require Coq.Classes.Morphisms.

Require Import Coq.Setoids.Setoid.

Require Import Turing.Turing.
Require Import Turing.LangDec.
Require Import Turing.LangRed.

Section A_TM. (* ----------------------------------------------- *)

  (* -------------------------------------------------------------------------- *)

  Definition A_tm : lang := fun i =>
    let (p, j) := decode_mach_input i in
    Run (Call p j) true.

  (**
    This new TM calls D to determine what M does when the input to M is its own
    description <M, <M>>. Once D has determined this information, it does the
    opposite. That is, it rejects if M accepts and accepts if M does not accept.

    The following is a description of [negator].
      negator = “On input <M>, where M is a TM :
          1. Run D on input <M, <M>>.
          2. Output the opposite of what D outputs.
            That is, if D accepts, reject ;
            and if D rejects, accept.”
  *)

  Definition negator solve_A_tm :=
    fun i =>
      mlet b <- solve_A_tm <[ decode_mach i, i ]> in
      if b then Ret false
           else Ret true
    .

  Lemma negator_accept:
    forall p n,
    CodeOf (negator p) n -> 
    Run (Call n [[ n ]]) true ->
    Run (p <[ n, [[ n ]] ]>) false.
  Proof.
    unfold negator.
    intros p n co Hr.
    run_simpl_all.
    inversion_clear Hr.
    destruct b1; run_simpl_all.
    assumption.
  Qed.

  Lemma negator_reject:
    forall p n,
    CodeOf (negator p) n ->
    Run (Call n [[ n ]]) false ->
    Run (p <[ n, [[ n ]] ]>) true.
  Proof.
    unfold negator.
    intros p n co Hr.
    run_simpl_all.
    inversion_clear Hr.
    destruct b1; run_simpl_all.
    assumption.
  Qed.

  Lemma negator_loop:
    forall d n,
    Decider d ->
    CodeOf (negator d) n ->
    ~ Loop (Call n [[n]]).
  Proof.
    unfold negator.
    intros d n cp cn N.
    run_simpl_all.
    inversion_clear N.
    - apply decider_to_not_loop in H; auto.
    - (* Cannot Loop on return *)
      destruct b; auto; inversion_clear H0.
  Qed.

  (** Theorem 4.11, pp 207 *)

  Theorem a_tm_undecidable:
    ~ Decidable A_tm.
  Proof.
    intros N.
    (* Suppose that D is a decider for A_TM. *)
    destruct N as (solve_A, is_dec).
    destruct is_dec as (Hrec, Hdec).
    (* Now we construct a new Turing machine [negator] with D as a subroutine. *)
    (* What happens when we run [negator] with its own description <negator> as
      input? *)
    destruct (code_of (negator solve_A)) as (n, Hn).
    destruct (run_exists (Call n [[n]]) ) as [([], He)|He];
      assert (Hx := He).
    (* (Let us duplicate Heqr as we will need it later.) *)
    - eapply negator_accept in He; eauto.
      eapply recognizes_run_false_to_not_in in He; eauto.
      contradict He.
      unfold A_tm.
      run_simpl_all.
      assumption.
    - eapply negator_reject in He; eauto.
      eapply recognizes_run_true_to_in in He; eauto.
      (* He: Run (negator D) [[negator D]] accept *)
      unfold A_tm in *.
      run_simpl_all.
    - eapply negator_loop in Hx; eauto.
  Qed.

  (* -------------------------------------------------------------------------- *)

  Lemma a_tm_recognizable: Recognizable A_tm.
  Proof.
    apply recognizable_def with (p:=fun p => 
      let (M, w) := decode_mach_input p in
      (* Calls program M with input w *)
      Call M w
    ).
    apply recognizes_def.
    intros.
    unfold A_tm.
    (* remove the pair *)
    destruct (decode_mach_input i) as (p, j).
    reflexivity.
  Qed.


  (** Corollary 4.23 *)

  Theorem co_a_tm_not_recognizable:
    ~ Recognizable (compl A_tm).
  Proof.
    intros N.
    assert (Hx : Recognizable A_tm /\ Recognizable (compl A_tm)). {
      split.
      - apply a_tm_recognizable.
      - assumption.
    }
    apply dec_rec_co_rec in Hx.
    apply a_tm_undecidable.
    assumption.
  Qed.

  (** *********************************************
      * Another proof of A_tm undecidable follows *
      *********************************************

      Show that A_tm is undecidable via map-reducibility to SELF_tm.
      Proof originally by Yannick Forster.
      
      This proof similar to Sipser's Theorem 6.5.
  *)

  (* Define the language of programs that accept their own code. *)

  Definition SELF_tm := fun i =>
    Run (Call (decode_mach i) i) true.

  (* 1. Show that the complement of SELF is unrecognizable.
  
    Proof.

    Assume by contradiction that some program p recognizes itself.
    Case analysis on the result of running the p on itself.
    
    1. ACCEPTS itself. (Recognizability) Since p recognizes co-SELF and
       p accepts itself, then p is in co-SELF.
       (Def of co-SELF) If p is in co-SELF and p recognizes co-SELF,
       then p must reject itself.

    2. REJECTS/LOOPS itself. (Recognizability) Since p recognizes co-SELF and
       p rejects/loops itself, then p is not in co-SELF.

       (Def of co-SELF) However, can also show that p IS in co-SELF:
       as we only need to show that p does not accept itself
       (which is given already). 
   *)

  Lemma co_self_tm_unrecognizable:
    ~ Recognizable (compl SELF_tm).
  Proof.
    intros N.
    destruct N as (f, Hr).
    destruct (code_of f) as (p, hp).
    (* By contradiction, assume that p recognizes co-SELF_TM *)
    destruct (run_true_or_negative (Call p (encode_mach p))) as [He|He];
    run_simpl_all;
    assert (Hx := He). (* Let us duplicate assumption Hx *)
    - (* If p accepts itself *)
      eapply recognizes_run_true_to_in in He; eauto.
      (* That means that p is in co-SELF *)
      unfold compl, SELF_tm in *.
      (* Since p is in co-self, then p should reject itself, which is an absurd  *)
      contradict He.
      run_simpl_all.
      assumption.
    - (* P rejects itself *)
      (* Thus, p is NOT in co-SELF *)
      assert (~ compl SELF_tm [[ p ]]) by eauto using recognizes_negative_to_not_in.
      (* But we can also conclude that compl SELF_tm [[ p ]] *)
      contradict H.
      unfold compl, SELF_tm.
      (* By contradiction, assume SELF_tm [[ p ]]  *)
      intros N. (* Thus, Run (decode_prog [[p]]) [[p]] true *)
      (* Since p is in co-self, then p must accept itself, thus absurd *)
      run_simpl_all.
  Qed.

  (* 3. Show that co-A_tm map-reduces to co-SELF_tm *)

  Lemma co_a_tm_red_co_self_tm:
    compl SELF_tm <=m compl A_tm.
  Proof.
    intros.
    (* Supply the mapping: *)
    exists (fun i => <[ decode_mach i, i ]>).
    unfold Reduction.
    intros.
    unfold A_tm, SELF_tm, compl; split; intros.
    - intros N1.
      contradict H.
      run_simpl.
      assumption.
    - intros N1.
      contradict H.
      run_simpl.
      assumption.
  Qed.

  (* 4. Show co-A_tm is unrecognizable.

     Proof via map-reducibility:
     - We know co-SELF is unrecognizable.
     - We know that co-SELF <= co-A.

   *)

  Theorem co_a_tm_unrecognizable:
    ~ Recognizable (compl A_tm).
  Proof.
    apply reducible_unrecognizable with (A:=compl SELF_tm).
    - apply co_a_tm_red_co_self_tm.
    - apply co_self_tm_unrecognizable.
  Qed.

  (* 5. A_tm is undecidable.

     Proof.

     We have shown that A_tm is recognizable
     we have shown that A_tm is not co-recognizable.
     Thus, A_tm cannot be decidable (Theorem 4.22).

   *)

  Theorem a_tm_undecidable_alt:
    ~ Decidable A_tm.
  Proof.
    intros N.
    apply dec_rec_co_rec in N.
    destruct N as (_, N).
    apply co_a_tm_unrecognizable; auto.
  Qed.

  (* -------------------------------------------------------------------------- *)

  End A_TM.


Section HALT_TM. (* ---------------------- Theorem 5.1 --------------------- *)

  Definition HALT_tm : lang := fun p =>
    let (M, w) := decode_mach_input p in
    Halt (Call M w).

  (** Theorem 5.1 *)
  Theorem HALT_tm_undecidable:
    ~ Decidable HALT_tm.
  Proof.
    intros N.
    destruct N as (solves_HALT, H).
    apply a_tm_undecidable.
    apply decidable_def with (p:=fun p =>
      let (M, w) := decode_mach_input p in
      mlet b <- solves_HALT p in
      if b then Call M w else Ret false 
    ).
    apply decides_def. {
      unfold A_tm.
      constructor; intros Ha. {
        destruct (decode_mach_input i) as (p, j) eqn:r1.
        inversion Ha; subst; clear Ha.
        destruct b1; run_simpl_all.
        assumption.
      }
      destruct (decode_mach_input i) as (p, j) eqn:r1.
      apply run_seq with (b1:=true). {
        apply decides_in_to_run_true with (L:=HALT_tm); auto.
        unfold HALT_tm.
        rewrite r1.
        eauto using run_to_halt.
      }
      assumption.
    }
    apply decider_def.
    intros.
    destruct (decode_mach_input i) as (p, j) eqn:r1.
    apply halt_seq_alt. {
      eauto using decides_to_halt.
    }
    intros.
    destruct b; try constructor.
    match goal with
    H: Run _ _ |- _ => rename H into Hc
    end.
    apply decides_run_true_to_in with (L:=HALT_tm) in Hc; eauto.
    unfold HALT_tm in *.
    rewrite r1 in *.
    assumption.
  Qed.

End HALT_TM. (* ------------------------------------------------------------ *)

Section E_TM. (* --------------------- Theorem 5.2 ------------------------- *)

  Definition E_tm : lang := fun i =>
    let p := decode_mach i in
    forall i, Negative (Call p i).

  Theorem E_tm_undecidable:
    ~ Decidable E_tm.
  Proof.
    intros HD.
    destruct HD as (solve_E, H).
    destruct (code_of solve_E) as (s, hs).
    apply a_tm_undecidable.
    destruct (closure_of (fun p x =>
        let (M, w) := decode_mach_input p in
          if input_eq_dec x w then (
            Call M w
          ) else Ret false
        )
      ) as (inner, Hr).
    apply decidable_def with (p:= fun p =>
        let (M, w) := decode_mach_input p in
        mlet b <- Call s [[ inner p ]] in
        if b then Ret false else Ret true
    ).
    apply decides_def. {
      apply recognizes_def; intros.
      (* Run implies in A_tm *)
      unfold A_tm.
      destruct (decode_mach_input i) as (p, j) eqn:r1.
      assert (rw1: Run (Call p j) true <-> Run (Call s [[ inner i ]]) false). {
        run_simpl_all.
        erewrite decides_false_rw; eauto.
        unfold E_tm.
        run_simpl.
        split; intros. {
          intros N.
          specialize (N j).
          rewrite (closure_of_negative_rw Hr) in N.
          rewrite r1 in *.
          destruct (input_eq_dec j j); try contradiction.
          rewrite negative_rw in *.
          contradiction.
        }
        destruct (run_true_or_negative (Call p j)) as [Ht|Hf]; auto.
        match goal with H: ~ (forall i, Negative _) |- _ =>
          contradict H
        end.
        intros k.
        rewrite (closure_of_negative_rw Hr) in *.
        rewrite r1.
        destruct (input_eq_dec k j). {
          subst.
          assumption.
        }
        apply negative_ret.
      }
      rewrite rw1; clear rw1.
      split; intros hr. {
        inversion_clear hr.
        run_simpl_all.
        destruct b1; run_simpl_all.
        assumption.
      }
      apply run_seq with (b1:=false); auto.
      constructor.
    }
    (* Prove that it halts *)
    apply decider_def.
    intros i.
    destruct (decode_mach_input i) as (p, j) eqn:hr1.
    apply halt_seq_alt. {
      run_simpl_all.
      eauto using decides_to_halt.
    }
    intros.
    destruct b; constructor.
  Qed.


End E_TM. (* --------------------------------------------------------------- *)

Section EQ_TM.
    (** Show that EQ_TM is unrecognizable and co-unrecognizable. *)

    (** We formally define EQ_TM: *)
    Definition EQ_tm := fun p =>
      let (w1, w2) := decode_pair p in
      let M1 := decode_mach w1 in
      let M2 := decode_mach w2 in
      forall i,
      Run (Call M1 i) true <-> Run (Call M2 i) true.

    Lemma co_a_tm_red_eq_tm:
      compl A_tm <=m EQ_tm.
    Proof.
      apply reducible_iff with (f:=fun p =>
        let (M, w) := decode_mach_input p in
        let M1 : input := [[ compile (Ret false) ]] in
        let M2 : input := [[ compile (Call M w) ]] in
        encode_pair (M1 , M2)
      ).
      unfold EQ_tm; split; intros.
      - unfold A_tm, compl in *.
        destruct (decode_mach_input w) as (M, x) eqn:Heq.
        run_simpl_all.
        intros.
        repeat rewrite compile_run_rw.
        split; intros. {
          run_simpl_all.
        }
        contradiction.
      - destruct (decode_mach_input w) as (M, x) eqn:Heq.
        run_simpl_all.
        intros N.
        specialize (H x).
        assert (Hm: Run (Call M x) true). {
          unfold A_tm in *.
          rewrite Heq in *.
          assumption.
        }
        clear N.
        repeat rewrite compile_run_rw in H.
        rewrite <- H in Hm.
        inversion Hm.
    Qed.

    Lemma a_tm_red_eq_tm:
      A_tm <=m EQ_tm.
    Proof.
      apply reducible_iff with (f:=fun p =>
        let (M, w) := decode_mach_input p in
        let M1 : input := [[ compile (Ret true) ]] in
        let M2 : input := [[ compile (Call M w) ]] in
        encode_pair (M1 , M2)
      ).
      unfold EQ_tm; split; intros.
      - destruct (decode_mach_input w) as (M, x) eqn:Heq.
        run_simpl_all.
        intros.
        run_simpl_all.
        split; intros; run_simpl_all.
        + unfold A_tm in *.
          rewrite Heq in *.
          assumption.
        + apply run_ret.
      - unfold A_tm.
        destruct (decode_mach_input w) as (M, x) eqn:Heq.
        run_simpl_all.
        specialize (H w).
        run_simpl_all.
        rewrite <- H.
        constructor.
    Qed.

    (** Theorem 5.30: EQ_TM is neither recognizable nor co-recognizable. *)

    Theorem eq_tm_not_recognizable: (** Theorem 5.30 *)
      ~ Recognizable EQ_tm.
    Proof.
      apply reducible_unrecognizable with (A:=compl A_tm); auto.
      - apply co_a_tm_red_eq_tm.
      - apply co_a_tm_not_recognizable.
    Qed.

    Theorem co_eq_tm_not_recognizable: (** Theorem 5.30 *)
      ~ Recognizable (compl EQ_tm).
    Proof.
      apply reducible_unrecognizable with (A:=compl A_tm); auto.
      - rewrite co_red_co_rw.
        apply a_tm_red_eq_tm.
      - apply co_a_tm_not_recognizable.
    Qed.

    Theorem eq_tm_not_decidable: (** Theorem 5.4 *)
      ~ Decidable EQ_tm.
    Proof.
      intros N.
      apply dec_rec_co_rec in N.
      destruct N as (N, _).
      apply eq_tm_not_recognizable in N.
      assumption.
    Qed.

End EQ_TM.

Section Rice. (* ----------------------------------------------------------- *)

  (*
    Proof by: Kleopatra Ginji, Tiago Cogumbreiro, and Yannick Forster
    Proof closely follows:
      http://homepages.gac.edu/~sskulrat/Courses/2011S-265/notes/ricesTheorem.pdf

  *)
  (* To solve Rice's theorem, we created RiceP theorem.
     Following Sipser, we are showing that P is decidable by deciding A_tm. Because 
     A_tm is undecidable then P is also undecidable. However, in this proof, we show how to decide
     HALT_tm instead of A_tm. *)

  Theorem RiceP (P : input -> Prop) :
    forall i,
    P i ->
    (forall M M' : machine, (forall i, Run (Call M i) true <-> Run (Call M' i) true) ->
                        P (encode_mach M) <-> P (encode_mach M')) ->
     ~ P [[compile(Ret false)]] ->
     ~ Decidable P.
  Proof.
    (* Rp is the decider. *)
    intros i HPi HEquiv Hx (P_impl, P_spec).
    (* Decide HALT_tm. *)
    apply HALT_tm_undecidable.
    (* Takes two parameters: runs the first parameter, followed by the second *)
    (* Construction of `seq` has the following description: 
       M_w = "On input string x: 
                a) Run M on w
                b) If M halts, run T on x. If it accepts, accept. If it rejects, reject.", 
       with M and T being Turing Machines and w and x string  inputs. *)
    destruct (closure_of (fun p x =>
      let (M, w) := decode_mach_input p in
      let T := decode_mach i in
      mlet _ <- Call M w in Call T x )
    ) as (seq, H_seq).
    (* The following turing machine  
       S = "On input <M, w>, where M is a TM and w is a string:
            1. Construct an encoding <M_w> of a TM M_w that works as M_w above,
            2. Run P_impl on <M_w>
            3. If (2) accepts, accept. If (2) rejects, reject." *)
    apply decidable_def with (p:=
      fun (p:input) => 
      P_impl [[seq p]]
    ).
    apply decides_def.
    2: {
      (*
        It is trivial to show that our program halts for all inputs,
        so we show it first.
      *)
      apply decider_def.
      intros k.
      eapply decides_to_halt; eauto.
    }
    (* We now show that our program recognizes HALT_tm *)
    apply recognizes_def.
    intros k.
    (* Simplify our goal to: P [[seq k]] <-> Halt (Call M w) *)
    unfold HALT_tm.
    destruct (decode_mach_input k) as (M, w) eqn: r1.
    rewrite (decides_true_rw P_spec).
    (* Now prove each side of the implication *)
    split; intros Hp. {
      (* Suppose [[seq k]] is in P *)
      clear HPi.
      (* Either M halts on w, or M loops on w. *)
      destruct (halt_or_loop (Call M w)) as [Hm|Hm]; auto.
      (* If it halts, we are done, so let us consider the former: M loops on w *)
      (* We can shoiw that seq <<M,w>> loops on all input. L(M_w) = empty set *)
      assert (Hmw : forall x, Loop (Call (seq k) x)). {
        intros.
        rewrite (closure_of_loop_rw H_seq).
        rewrite r1.
        apply loop_seq_l.
        assumption.
      }
      contradict Hx.
      (* L(M_w) = L(T_empty), then <T_empty> does not belong in P by supposition. Therefore,
         by the second condition assumption <M_w> does not belong in P either. *)
      apply HEquiv with (M:= seq k); auto.
      intros j.
      split; intros; run_simpl_all.
      specialize (Hmw j).
      apply run_to_halt in H.
      run_simpl_all.
    }
    (* Suppose M halts on w. *)
    (* Running M an any input x is exactly like running T on the same input x. *)
    apply HEquiv with (M:= decode_mach i).
    2: { run_simpl_all. assumption. }
    (* L(M_w) = L(T). <T> belongs in P, therefore, by the second condition assumption <M_w> 
       also belongs in P. *)
    intros l; split; intros Hl.
    (* R accepts <M_w>. Thus, S also accepts <M_w>. *)
    + rewrite (closure_of_run_rw H_seq).
      rewrite r1.
      rewrite halt_rw in Hp.
      destruct Hp as (b, Hr).
      apply run_seq with b; auto.
    + rewrite (closure_of_run_rw H_seq) in *.
      rewrite r1 in *.
      inversion_clear Hl.
      assumption.
Qed.

  Inductive Nontrivial (P:input -> Prop) : Prop :=
    | non_trivial_def:
      forall i j,
      P i ->
      ~ P j ->
      Nontrivial P
    .


  Theorem Rice (P : input -> Prop) (nt: Nontrivial P):
    (forall M M' : machine, (forall i, Run (Call M i) true <-> Run (Call M' i) true) ->
                        P (encode_mach M) <-> P (encode_mach M')) ->
    ~ Decidable P.
  Proof.
    intros HEquiv Hp.
    inversion nt as [i j Hpi Hpj].
    (* If we can show that ~P is undecidable then we can conclude that P is undecidable since
       decidable languages are closed under complementation*)
    assert (Hx: P [[compile (Ret false)]] \/ ~P [[compile (Ret false)]]). {
      destruct Hp.
      eapply decides_or; eauto.
    }
    (* The ~P [[Ret false]] case. *)
    destruct Hx as [Hx|Hx]. 2: {
      contradict Hp.
      (* Apply RiceP, see theorem and details above. *)
      eapply RiceP; eauto.
    }
    (* We assume the case where <T_empty> does not belong to the complement of P. *)
    assert (H: ~ Decidable (compl P)). {
      (* Apply the theorem RiceP in the case of the complement as we did before for P. *)
      apply RiceP with j.
       - unfold compl.
         assumption.
       - intros; unfold compl.
         split; intros.
         + intros N.
           contradict H0.
           apply HEquiv with (M:= M'); auto.
           intros x.
           rewrite H; reflexivity.
         + contradict H0.
           apply HEquiv with (M:= M).
           * intros x.
             rewrite H; reflexivity.
           * assumption.
       - intros N.
         contradiction.
    }
    apply decidable_to_compl in Hp.
    contradiction.
  Qed.

End Rice. (* ---------------------------------------------------------------- *)
