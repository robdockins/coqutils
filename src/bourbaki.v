(* Robert Dockins (c) 2013.

   Proof of the Bourbaki-Witt fixpoint theorem, adapted
   for preorders.  The fixpoint theorem can then be used to
   prove Zorn's lemma from the axiom of choice.

   This proof strategy is based on online lecture notes:
   Lectures originally given by Imre Leader in 2003. Notes by John Fremlin.

   NB: This theorem makes extensive use of EM.  There is no hope
   to remove it as there can be no constructive proof of this theorem.
   See: Bauer, 2009. "On the Failure of Fixed-Point Theorems for
          Chain-complete Lattices in the Effective Topos."
 *)

Require Import ClassicalFacts.
Require Import ChoiceFacts.

Section bourbaki.
  Hypothesis classic : excluded_middle.

  Variable A:Type.
  Variable R:A -> A -> Prop.

  Hypothesis Rrefl : forall a, R a a.
  Hypothesis Rtrans : forall a b c,
    R a b -> R b c -> R a c.

  Definition ordered_set (T:A -> Prop) :=
    forall x y, T x -> T y -> R x y \/ R y x.

  Definition upper_bound (T:A -> Prop) (bnd:A) :=
    forall x, T x -> R x bnd.

  Definition least_upper_bound (T:A -> Prop) (bnd:A) :=
    upper_bound T bnd /\
    forall bnd', upper_bound T bnd' -> R bnd bnd'.

  Hypothesis chain_complete : 
    forall T t, ordered_set T -> T t ->
      exists bnd, least_upper_bound T bnd.
  
  Definition inflationary (f:A -> A) :=
    forall x, R x (f x).

  Section fixpoint.

    Variable f: A -> A.
    Hypothesis f_inflate : inflationary f.
    Hypothesis f_iso : forall x y,
      R x y -> R y x -> R (f x) (f y).

    Variable x0:A.
  
    Record closed (B:A -> Prop) : Prop :=
    { cl_incl : B x0
    ; cl_iso : forall x y, R x y -> R y x -> B x -> B y
    ; cl_f : forall x, B x -> B (f x)
    ; cl_chain : forall T t,
        ordered_set T -> T t ->
        (forall x, T x -> B x) ->
        exists bnd,
          B bnd /\
          least_upper_bound T bnd
    }.

    Definition all_closed (x:A) : Prop :=
      forall B, closed B -> B x.

    Lemma all_closed_closed : closed all_closed.
    Proof.
      constructor.
      hnf; intros. apply (cl_incl B); auto.
      repeat intro.
      apply (cl_iso B) with x; auto.
      apply (H1 B); auto.
      repeat intro. apply (cl_f B); auto.
      apply (H B); auto.
      
      intros.
      destruct (chain_complete T t H H0).
      destruct H2.
      exists x. split. 
      2: split; auto.
      intros B HB.
      destruct (cl_chain B) with T t; auto.
      intros.
      apply H1; auto.
      destruct H4 as [?[??]].
      apply (cl_iso B) with x1; auto.
    Qed.
    
    Lemma closed_restrict : forall B,
      closed B -> closed (fun x => B x /\ R x0 x).
    Proof.
      intros.
      constructor.
      split; auto. apply H.
      intros.
      destruct H2. split.
      apply (cl_iso B) with x; auto.
      apply Rtrans with x; auto.
      intros.
      destruct H0. split; auto.
      apply (cl_f B); auto.
      apply Rtrans with x; auto.
    
      intros.
      destruct (cl_chain B) with T t; auto.
      intros. destruct (H2 x); auto.
      destruct H3.
      exists x. split; auto.
      split; auto.
      destruct H4.
      apply Rtrans with t.
      destruct (H2 t); auto.
      apply H4; auto.
    Qed.
    
    Lemma all_closed_x0 : forall x,
      all_closed x -> R x0 x.
    Proof.
      intros.
      generalize (H (fun x => all_closed x /\ R x0 x)).
      intro. destruct H0; auto.
      apply closed_restrict.
      apply all_closed_closed.
    Qed.

    Definition normal x :=
      all_closed x /\
      forall y, all_closed y -> 
        R y x -> R x y \/ R (f y) x.

    Section normal1.
      Variables x y:A.
      Hypothesis Hx : normal x.
      Hypothesis Hy : all_closed y.

      Let outer z := all_closed z /\ (R z x \/ R (f x) z).

      Lemma outer_closed : closed outer.
      Proof.
        constructor. 
        hnf. 
        destruct Hx.
        split. apply (cl_incl all_closed).
        apply all_closed_closed.
        left.
        apply all_closed_x0.
        destruct Hx; auto.

        intros.
        destruct H1.
        split; auto.
        apply (cl_iso all_closed) with x1; auto.
        apply all_closed_closed.
        destruct H2.
        left. apply Rtrans with x1; auto.
        right. apply Rtrans with x1; auto.
        intros.
        destruct H.
        split.
        apply (cl_f all_closed); auto.
        apply all_closed_closed.
        destruct H0.
        destruct Hx.
        destruct (H2 x1); auto.
        right. apply Rtrans with x1; auto.

        intros.
        destruct (cl_chain all_closed) with T t as [bnd ?]; auto.
        apply all_closed_closed.
        intros.
        destruct (H1 x1); auto.
        destruct H2.
        exists bnd. split; auto.
        split; auto.
        destruct (classic (exists y, T y /\ R x y /\ ~R y x)).
        destruct H4 as [q [?[??]]].
        destruct (H1 q); auto.
        destruct H8; auto. contradiction.
        right. apply Rtrans with q; auto.
        destruct H3. apply H3; auto.
        left. destruct H3.
        apply H5.
        hnf; intros.
        destruct (classic (R x1 x)); auto.
        destruct (H1 x1); auto.
        destruct H9; auto.
        elim H4.
        exists x1. split; auto. split; auto.
        apply Rtrans with (f x); auto.
      Qed.

      Lemma normal1 : R y x \/ R (f x) y.
      Proof.
        assert (outer y).
        apply (Hy outer). apply outer_closed.
        destruct H; auto.
      Qed.
    End normal1.

    Lemma normal2 : closed normal.
    Proof.
      constructor.
      split. apply (cl_incl all_closed).
      apply all_closed_closed.
      intros.
      left. apply all_closed_x0. auto.
      intros.
      destruct H1. split.
      apply (cl_iso all_closed) with x; auto.
      apply all_closed_closed.
      intros.
      destruct (H2 y); auto.
      apply (cl_iso all_closed) with x; auto.
      apply all_closed_closed.
      destruct (H2 y0); auto.
      apply Rtrans with y; auto.
      left. apply Rtrans with x; auto.
      right. apply Rtrans with x; auto.
      destruct (H2 y0); auto.
      apply Rtrans with y; auto.
      left. apply Rtrans with x; auto.
      right. apply Rtrans with x; auto.

      intros. destruct H; split; auto.
      apply (cl_f all_closed); auto.
      apply all_closed_closed.
      intros.
      destruct (normal1 x y); auto.
      split; auto.
      destruct (H0 y); auto.
      right. apply Rtrans with x; auto.

      intros.
      destruct (cl_chain all_closed) with T t as [s ?]; auto.
      apply all_closed_closed.
      intros. destruct (H1 x); auto.
      destruct H2.
      exists s; split; auto.
      split; auto.
      intros.
      destruct (classic (R s y)); auto.
      right.

      destruct (classic (exists x, T x /\ ~R x y)).
      destruct H7 as [x [??]].
      destruct (normal1 x y); auto.
      destruct (H1 x); auto.
      destruct (H11 y); auto.
      elim H8; auto.
      apply Rtrans with x; auto.
      destruct H3. apply H3; auto.
      elim H8. apply Rtrans with (f x); auto.
      assert (forall x, T x -> R x y).
      intros. destruct (classic (R x y)); auto.
      elim H7; eauto.
      destruct H3.
      elim H6.
      apply H9.
      auto.
    Qed.

    Lemma all_closed_chain : ordered_set all_closed.
    Proof.
      hnf; intros.
      destruct (normal1 x y); auto.
      apply (H normal). apply normal2; auto.
      left. apply Rtrans with (f x); auto.
    Qed.

    Theorem bourbaki :
      exists x, R x0 x /\ R x (f x) /\ R (f x) x.
    Proof.
      destruct (cl_chain all_closed) with all_closed x0.
      apply all_closed_closed.
      apply all_closed_chain.
      hnf; intros. apply (cl_incl B); auto.
      auto.
      exists x.
      destruct H. destruct H0.
      split.
      apply all_closed_x0. auto.
      split; auto.
      apply H0.
      apply (cl_f all_closed); auto.
      apply all_closed_closed.
    Qed.
  End fixpoint.

  Definition maximal x :=
    forall y, R x y -> R y x.

  Definition is_quot (P:A -> Prop) :=
    (exists a, P a) /\
    (forall x y, P x -> P y -> R x y /\ R y x).

  Definition quot := { P:A -> Prop | is_quot P }.

  Program Definition q (x:A) : quot :=
    fun y => R x y /\ R y x.
  Next Obligation.
    split. exists x; split; auto.
    intuition eauto.
  Qed.

  Hypothesis prop_ext : prop_extensionality.
  Hypothesis fun_ext : forall A B (f g:A -> B),
    (forall x, f x = g x) -> f = g.
  Hypothesis choose: FunctionalChoice.

  Lemma q_eq : forall x y,
    R x y -> R y x -> q x = q y.
  Proof.
    intros. unfold q.
    generalize (q_obligation_1 x).    
    generalize (q_obligation_1 y).
    replace (fun y0 => R x y0 /\ R y0 x)
      with (fun y0 => R y y0 /\ R y0 y).
    intros. f_equal.
    apply ext_prop_dep_proof_irrel_cic; auto.
    apply fun_ext.
    intro. apply prop_ext.
    intuition eauto.
  Qed.

  Theorem zorn :
    forall x0:A, exists x, maximal x.
  Proof.
    intro x0.
    destruct (classic (exists x, maximal x)); auto.
    elimtype False.
    set (R' (qx qy:quot) :=
      forall x y, proj1_sig qx x -> proj1_sig qy y ->
        R x y /\ ~R y x).
    destruct (choose quot quot R') as [f ?].
    intro.
    destruct (classic (exists y, R' x y)); auto.
    elim H.
    destruct x as [P [??]]; simpl in *.
    destruct e. exists x. hnf; intros.
    destruct (classic (R y x)); auto.
    elim H.
    elim H0.
    exists (q y).
    hnf. simpl; intros.
    destruct H4. split.
    destruct (a x x1); eauto.
    intro. apply H2.
    destruct (a x x1); eauto.

    set (R'' x y := proj1_sig (f (q x)) y).
    destruct (choose A A R'') as [f' ?].
    intros.
    case_eq (f (q x)); simpl; intros.
    destruct i. destruct e.
    exists x2. red.
    rewrite H1; simpl. auto.
    destruct (bourbaki f') with x0.

    hnf; intros.
    generalize (H1 x).
    intros. red in H2.
    generalize (H0 (q x)).
    intros. hnf in H3.
    simpl in H3.
    destruct (H3 x (f' x)); auto.

    intros.
    generalize (H1 x). generalize (H1 y).
    unfold R''; simpl; intros.
    assert (q x = q y). apply q_eq; auto.
    rewrite H6 in H5.
    destruct (f (q y)); simpl in *.
    destruct i.
    destruct (H8 (f' x) (f' y)); auto.

    destruct H2 as [?[??]].
    generalize (H1 x). intro.
    red in H5.
    generalize (H0 (q x)). unfold R'; simpl; intros.
    destruct (H6 (f' x) (f' x)); auto.
  Qed.

End bourbaki.
