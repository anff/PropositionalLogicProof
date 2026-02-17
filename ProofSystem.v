From Coq Require Import List.
Import ListNotations.

From PropLogic Require Import Syntax Semantics.
Import Syntax.Syntax Semantics.Semantics.

Module ProofSystem.

Inductive derives : list formula -> formula -> Prop :=
(*  Tautology rule *)
| D_Taut: forall Γ p, tautology p -> derives Γ p 

(* anything in Γ is derivable from Γ *)
| D_In: forall Γ p, In p Γ -> derives Γ p

(* Modus Ponens *)
| D_MP: forall Γ p q, derives Γ (p → q) ->
    derives Γ p ->
    derives Γ q.

Notation "Γ ⊢ p" := (derives Γ p) (at level 70).

End ProofSystem.


