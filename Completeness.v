From Coq Require Import List Classical.
Import ListNotations.

From PropLogic Require Import Syntax Semantics ProofSystem Soundness.
Import Syntax.Syntax Semantics.Semantics ProofSystem.ProofSystem Soundness.Soundness.
 
Module Completeness.

Ltac prove_taut :=
  unfold tautology; intros; simpl.

Theorem weakening_cons: forall (Γ : list formula) (p q : formula),
  Γ ⊢ q -> (p :: Γ) ⊢ q.
Proof.
  intros Γ p q H.
  induction H.
  - apply D_Taut. auto. 
  - apply D_In. apply in_cons. exact H.
  - apply D_MP with (p := p0). 
    -- easy.
    -- easy.
Qed.

(* Leamma 3.2.2 *)
Theorem deduction_rule: 
  forall (Γ : list formula) (p q : formula), (p :: Γ) ⊢ q <-> Γ ⊢ (p → q).
Proof.
  intros Γ p q. 
  split.
  (* p :: Γ ⊢ q -> Γ ⊢ (p → q) *)
  - intros H.
    remember (p :: Γ) as pΓ eqn:HΓ in H.
    induction H as [pΓ q | pΓ q | pΓ q].
    
    (* Hypo: tautology q.
       Goal: Γ ⊢ (p → q) *)
    -- assert (H1: (tautology q) -> tautology (p → q)).
      --- prove_taut. specialize (H0 V). tauto.
      --- apply H1 in H. 
          apply D_Taut. easy.
   
    (* Hypo: In q pΓ
       Goal: Γ ⊢ (p → q) *)
    -- rewrite HΓ in H. simpl in H.
      destruct H as [H1 | H1].
      --- rewrite H1. apply D_Taut. prove_taut. tauto.
      --- apply D_In in H1. 
          assert (H2: Γ ⊢ (q → (p → q))).
          + apply D_Taut. prove_taut. tauto.
          + apply D_MP with (p := q). easy. easy.
    
    (* H0: pΓ ⊢ q
       IHderives1: pΓ = p :: Γ -> Γ ⊢ (p → q → q0)
       IHderives2: pΓ = p :: Γ -> Γ ⊢ (p → q)
       Goal: Γ ⊢ (p → q0) *)
    -- specialize (IHderives1 HΓ).
      specialize (IHderives2 HΓ). 
      assert (H1: Γ ⊢ ((p → q → q0) → ((p → q) → (p → q0)))).
      --- apply D_Taut. prove_taut. tauto.
      --- apply D_MP with (p := p → q → q0) in H1.
        ---- apply D_MP with (p := p → q) in H1. easy. easy.
        ---- easy.

  (* Goal: Γ ⊢ (p → q) -> p :: Γ ⊢ q *)
  - intros H.
    assert (H1: (p :: Γ) ⊢ p).
    -- apply D_In. 
       constructor. easy.
    -- assert (H2: (p :: Γ) ⊢ (p → q)).
      --- apply weakening_cons with (p := p) in H. easy.
      --- apply (D_MP (p :: Γ) p q) in H1.
        easy. 
        easy.
Qed.

(* 3.2.3 *)
Definition inconsistent (Γ : list formula) : Prop := 
  exists p, Γ ⊢ p /\ Γ ⊢ ¬ p.

(* 3.2.4 *)
Theorem derive_from_inconsistency: 
  forall (Γ : list formula) (p : formula), Γ ⊢ p <-> inconsistent ((¬ p) :: Γ).
Proof.
  intros Γ p. 
  split.
  (* Γ ⊢ p -> inconsistent (¬ p :: Γ) *)
  - intros H. 
    assert (H1: (¬ p :: Γ) ⊢ p). apply weakening_cons. easy.
    assert (H2: (¬ p :: Γ) ⊢ ¬ p). apply D_In. constructor. easy.
    -- unfold inconsistent. 
       exists p. split.
       easy. easy.
  
  (* inconsistent (¬ p :: Γ) -> Γ ⊢ p *)
  - intros H.
  unfold inconsistent in H. 
  destruct H as [q].
  destruct H as [H H1].
  apply deduction_rule in H.
  apply deduction_rule in H1.
  assert (H2: Γ ⊢ ((¬ p → q) → ((¬ p → ¬ q) → p))).
    -- apply D_Taut. prove_taut. tauto.
    -- apply (D_MP Γ (¬ p → q)) in H2.
      --- apply (D_MP Γ (¬ p → ¬ q)) in H2. easy. easy.
      --- easy.
Qed.

(* 3.2.5 *)
Definition complete (Γ : list formula) : Prop := 
  forall p, Γ ⊢ p \/ (Γ ⊢ (¬ p)).

(* Γ1 is subset of Γ *)
Definition is_subset (Γ1 Γ : list formula) : Prop :=
  forall p, In p Γ1 -> In p Γ.

Notation "G ⊆ Q" := (is_subset G Q) (at level 55, right associativity).

(* 3.2.6 *)
Lemma Lindenbaum: forall (Γ1 : list formula), 
  (~ inconsistent Γ1) -> (exists Γ, Γ1 ⊆ Γ /\ (~ inconsistent Γ) /\ (complete Γ)).
Proof.
Admitted.


(* Generate the evalution model for the given theory Γ *)
Definition build_valuation (Γ : list formula) : valuation := 
  fun p => Γ ⊨ p. 


(* 3.2.7 *)
(* sublemma, prove the negation case for Γ ⊢ p <-> evaluates V p *)
Lemma canonical_model_soundness_neg: forall (Γ : list formula) (p : formula) (V : valuation),
  (~ inconsistent Γ) /\ (complete Γ)
  -> (Γ ⊢ p) <-> (evaluates V p)  
  -> (Γ ⊢ (¬ p) <-> evaluates V (¬ p)).
Proof.
  intros Γ p V Htot IH.
  destruct Htot as [H1 H2].
  split.
  
  (* Γ ⊢ (¬ p) -> evaluates V (¬ p) *) 
  - intros H.
    destruct IH as [IHp1 IHp2].
    simpl. unfold not.
    intros Heval.
    specialize (IHp2 Heval).
    assert (Hincon : inconsistent Γ).
      { unfold inconsistent. exists p. split; assumption. }
    contradiction.

  (* Γ ⊢ (¬ p) <- evaluates V (¬ p) *) 
  - intros H.
    destruct IH as [IHp1 IHp2].
    simpl in H. 
    specialize (H2 p).
    -- destruct H2 as [H2p | H2n].
      + exfalso. 
        apply H. 
        apply IHp1.
        exact H2p.
      + exact H2n. 
Qed.

(* sublemma, prove the and case for Γ ⊢ p <-> evaluates V p *)
Lemma canonical_model_soundness_and: forall (Γ : list formula) (p1 p2 : formula) (V : valuation),
  (~ inconsistent Γ) /\ (complete Γ)
  -> (Γ ⊢ p1) <-> (evaluates V p1) 
  -> (Γ ⊢ p2) <-> (evaluates V p2) 
  -> (Γ ⊢ (p1 ∧ p2) <-> evaluates V (p1 ∧ p2)). 
Proof.
  intros Γ p1 p2 V Htot IH1 IH2.
  split.
  (* Γ ⊢ p1 ∧ p2 -> evaluates V (p1 ∧ p2) *)
  - intros H. 
    assert (Ht1: Γ ⊢ (p1 ∧ p2 → p1)).
      {apply D_Taut. prove_taut. tauto. }
    
    assert (Ht2: Γ ⊢ (p1 ∧ p2 → p2)). 
      {apply D_Taut. prove_taut. tauto. }
  
    apply (D_MP Γ (p1 ∧ p2)) in Ht1. apply IH1 in Ht1. 
    apply (D_MP Γ (p1 ∧ p2)) in Ht2. apply IH2 in Ht2.
    -- simpl. split. easy. easy.
    -- easy. 
    -- easy.

  (* Γ ⊢ p1 ∧ p2 <- evaluates V (p1 ∧ p2) *)
  - intros H. 
    simpl in H. 
    destruct H as [Ht1 Ht2].
    apply IH1 in Ht1.
    apply IH2 in Ht2.
    assert (Htau: Γ ⊢ (p1 → (p2 → (p1 ∧ p2)))).
      {apply D_Taut. prove_taut. tauto. }
    apply (D_MP Γ p1) in Htau.
    apply (D_MP Γ p2) in Htau. 
    easy. easy. easy.
Qed.

Lemma de_morgan_eval (V : valuation) (p1 p2 : formula) :
  ~ ( ~ evaluates V p1 /\ ~ evaluates V p2)
  <-> evaluates V p1 \/ evaluates V p2.
Proof.
  split.
  - (* -> direction *)
    intros H.
    destruct (classic (evaluates V p1)) as [Hp1 | Hp1].
    + left; exact Hp1.
    + destruct (classic (evaluates V p2)) as [Hp2 | Hp2].
      * right; exact Hp2.
      * exfalso. apply H. split; assumption.
  - (* <- direction *)
    intros Hor Hneg.
    destruct Hor as [Hp1 | Hp2];
    destruct Hneg as [Hnp1 Hnp2]; contradiction.
Qed.

(* Lemma to prove Γ ⊢ p <-> evaluates V p *)
Lemma canonical_model_soundness: forall (Γ : list formula),
  (~ inconsistent Γ) /\ (complete Γ)
  -> exists V, (forall p, Γ ⊢ p <-> evaluates V p).
Proof.
  intros Γ H.
  remember (build_valuation Γ) as V eqn:EqV.
  exists V.
  intros p. induction p as [p1 IH1 p2 IH2 | p1 IH1 p2 IH2 | p IH].

  (* Γ ⊢ p1 ∧ p2 <-> evaluates V (p1 ∧ p2) *)
  - apply (canonical_model_soundness_and Γ p1 p2 V) in H.
    exact H.
    easy. 
    easy.

  (* Γ ⊢ p1 v p2 <-> evaluates V (p1 v p2) *)
  - apply (canonical_model_soundness_neg Γ p1 V) in IH1.
    apply (canonical_model_soundness_neg Γ p2 V) in IH2.
    pose proof (canonical_model_soundness_and Γ (¬ p1) (¬ p2) V H IH1 IH2) as H3.
    apply (canonical_model_soundness_neg Γ (¬ p1 ∧ ¬ p2) V) in H3.
    assert (Htmp1: Γ ⊢ (¬ (¬ p1 ∧ ¬ p2) → (p1 v p2))).
      {apply D_Taut. prove_taut. tauto. }

    assert (H_eval2der : evaluates V (¬ (¬ p1 ∧ ¬ p2)) -> Γ ⊢ p1 v p2).
      {intros Heval. apply H3 in Heval. apply (D_MP Γ (¬ (¬ p1 ∧ ¬ p2))) in Htmp1. easy. easy. }
    
    assert (Htmp2: Γ ⊢ ((p1 v p2) → ¬ (¬ p1 ∧ ¬ p2))).
      {apply D_Taut. prove_taut. tauto. }
    
    assert (H_der2eval :  Γ ⊢ p1 v p2 -> evaluates V (¬ (¬ p1 ∧ ¬ p2)) ).
      {intros Heval. apply H3. apply (D_MP Γ (p1 v p2)) in Htmp2. easy. easy. }
    
    split.
    -- intros H0. apply H_der2eval in H0. apply de_morgan_eval in H0. simpl. easy.
    -- intros H0. apply H_eval2der. apply de_morgan_eval. simpl in H0. easy.
    -- easy.
    -- easy.
    -- easy.

  (* Γ ⊢ (¬ p) <- evaluates V (¬ p) *) 
  - apply (canonical_model_soundness_neg Γ p V) in H.
    exact H.
    easy.
Qed.

Lemma soundness_of_valuation : forall (Γ : list formula),
  (exists (V : valuation), forall p, Γ ⊢ p <-> evaluates V p) ->
  exists (V : valuation), satisfies V Γ.
Proof.
  intros Γ H.
  destruct H as [V H].
  exists V.
  unfold satisfies.
  eapply Forall_forall.
  intros p H0.
  apply (D_In Γ p) in H0.
  apply (H p) in H0.
  easy.
Qed.

(* Theorem 3.2.8 *)
Theorem completeness_form2 : 
  forall (Γ : list formula), 
  ~ inconsistent Γ 
  -> exists (V : valuation), satisfies V Γ.
Proof.
  intros Γ0 H.
  apply Lindenbaum in H.
  destruct H as [Γ H].
  destruct H as [H0 H1].

  (* for consistent and complete theoty,
  exists model V,
  Γ ⊢ p <-> evaluates V p *)
  apply (canonical_model_soundness Γ) in H1.

  (* V is the model of Γ *)
  apply (soundness_of_valuation Γ) in H1.

  destruct H1 as [V H1].
  exists V.
  unfold satisfies in *.
  rewrite Forall_forall in *.

  (* decompose the goal, intorduce p *)
  intros p H2.
  apply H0 in H2.
  apply (H1 p) in H2.
  easy.
Qed.

Lemma completeness_form2_contrapositive :
  forall (Γ : list formula),
    (~ exists V : valuation, satisfies V Γ) 
    -> inconsistent Γ.
Proof.
  intros Γ H.
  apply NNPP.                        
  intros H1.       
  apply H.
  apply completeness_form2.
  exact H1.
Qed.


Theorem completeness_form1 :
  forall (Γ : list formula) (p : formula),
    Γ ⊨ p -> Γ ⊢ p.
Proof.
  intros Γ p Hsat.

  (* Turns goal to: inconsistent (¬ p :: Γ) *)
  apply (derive_from_inconsistency Γ p).

  (* Turn goals to: no model satisfies ¬ p :: Γ *)
  apply completeness_form2_contrapositive.

  (* From Γ ⊨ p, Prove no models 
  satisfies ¬ p :: Γ *)
  intros H.
  destruct H as [V H].

  assert (HΓ: satisfies V Γ).
  { unfold satisfies in *. 
    rewrite Forall_forall in H.
    apply Forall_forall.
    intros q H0.
    apply (H q).
    right. easy. 
  }

  (* satisfies V Γ, and Γ ⊨ p 
  => V evaluates p.
  satisfies V (¬ p :: Γ)
  => V evaluates ¬ p.
  Contradiction. *)

  (* From Γ ⊨ p and satisfies V Γ,
  prove V evaluates p *)
  unfold entails in Hsat.
  specialize (Hsat V HΓ).

  (* from satisfies V (¬ p :: Γ) 
  =>  V evaluates ¬ p *)
  unfold satisfies in H.
  rewrite Forall_forall in H.
  assert (H1: In (¬ p) (¬ p :: Γ)).
    {left. easy. }
  specialize (H (¬ p) H1).
  simpl in H.
  apply H.
  easy.
Qed.

End Completeness.