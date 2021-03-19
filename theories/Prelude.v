From stdpp Require Export prelude.

Global Hint Mode Equiv ! : typeclass_instances.

(* Class LeftInv {A} (R : relation A) (i: A) (f: A -> A -> A) (inv: A -> A): Prop := *)
(*   left_inv x : R (f (inv x) x) i. *)
(* Class RightInv {A} (R : relation A) (i: A) (f: A -> A -> A) (inv: A -> A): Prop := *)
(*   right_inv x : R (f x (inv x)) i. *)

(* Global Arguments left_inv {_ _} _ _ _ {_} _ : assert. *)
(* Global Arguments right_inv {_ _} _ _ _ {_} _ : assert. *)

Declare Scope nominal_scope.
Delimit Scope nominal_scope with nom.
Open Scope nominal_scope.

