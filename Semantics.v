From Coq Require Import List Classical.
Import ListNotations.

From PropLogic Require Import Syntax.
Import Syntax.Syntax.

Module Semantics.

(* A valuation assigns each propositional variable a Prop. *)
Definition valuation : Type := formula -> Prop.

Fixpoint evaluates (V : valuation) (p : formula) : Prop :=
  match p with
  | And a b    => evaluates V a /\ evaluates V b
  | Or  a b    => evaluates V a \/ evaluates V b
  | Not a      => ~ evaluates V a
  end.

Definition satisfies (V : valuation) (Γ : list formula) : Prop :=
  Forall (fun p => evaluates V p) Γ.

Definition entails (Γ : list formula) (p : formula) : Prop :=
  forall V, satisfies V Γ -> evaluates V p.

Notation "Γ ⊨ p" := (entails Γ p) (at level 70).

Definition tautology (p : formula) : Prop :=
  forall V : valuation, evaluates V p.

End Semantics.

