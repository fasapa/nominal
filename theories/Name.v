From Nominal Require Export Prelude.
From stdpp Require Export listset countable infinite.

Module Type ATOMIC.
  Parameter t : Set.

  (* Contable? *)
  Axiom dec : EqDecision t.
  Axiom inf : Infinite t.
End ATOMIC.

Module Atom : ATOMIC.
  Definition t := nat.

  #[export] Instance dec : EqDecision t := nat_eq_dec.
  #[export] Instance inf : Infinite t := nat_infinite.
End Atom.
#[export] Existing Instances Atom.dec Atom.inf.

Notation name := Atom.t.

(* Finite set of names *)
Definition nameset := (listset name).