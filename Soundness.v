From Coq Require Import List Classical.
Import ListNotations.

From PropLogic Require Import Syntax Semantics ProofSystem.
Import Syntax.Syntax Semantics.Semantics ProofSystem.ProofSystem.

Module Soundness.

Lemma satisfy_tautology: forall (Γ : list formula) (p : formula), 
  tautology p -> Γ ⊨ p.
Proof.
  unfold entails.
  intros Γ p H V Hsat.
  (* Using def of tautology *)
  apply H.
Qed.

Lemma satisfy_model_members: forall (Γ : list formula) (p : formula), 
  In p Γ -> Γ ⊨ p.
Proof.
  unfold entails.
  intros Γ p H V Hsat.
  eapply Forall_forall in Hsat.
  - apply Hsat.
  - apply H.
Qed.  

Lemma satisfy_model_mp: forall (Γ : list formula) (p q : formula), 
  (Γ ⊨ p) /\ (Γ ⊨ (p → q)) -> Γ ⊨ q.
Proof.
  intros Γ p q H. 
  destruct H as [H0 H1].
  unfold entails in *.
  intros V Hsat.
  specialize (H0 V Hsat).
  specialize (H1 V Hsat).
  simpl in H1.
  
  destruct H1 as [H1 | H2].
  - contradiction.
  - apply H2.
Qed. 
  
Theorem soundness :
  forall (Γ : list formula) (p : formula), 
  Γ ⊢ p -> Γ ⊨ p.
Proof.
  intros Γ p H.
  induction H.
  
  - (* p is tautology *)
    apply (satisfy_tautology Γ p) in H. 
    easy.

  - (* p is in Γ *) 
    apply (satisfy_model_members Γ p) in H. 
    easy. 

  - (* using MP *)
    apply (satisfy_model_mp Γ p q). 
    split.
    -- apply IHderives2.
    -- apply IHderives1.
Qed. 

End Soundness.
