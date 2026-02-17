From Coq Require Import List.
Import ListNotations.

Module Syntax.

(* The connectors for the well-formed formulas *)
Inductive formula : Type :=
| And : formula -> formula -> formula
| Or  : formula -> formula -> formula
| Not : formula -> formula.
Infix  "∧" := And (at level 60, right associativity).
Infix  "v" := Or (at level 65, right associativity).
Notation "¬ p" := (Not p) (at level 55, right associativity).

Definition Imp (p q : formula) : formula := (¬ p) v q. 
Infix  "→" := Imp (at level 70, right associativity).

End Syntax.

