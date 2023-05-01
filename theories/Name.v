From Nominal Require Export Prelude.
From Coq Require Import Arith.Peano_dec.
From stdpp Require Export listset countable infinite.

Module Type ATOMIC.
  Parameter t : Set.

  (* Contable? *)
  Axiom dec : EqDecision t.
  Axiom inf : Infinite t.

  Axiom default: t.
End ATOMIC.

Module Atom : ATOMIC.
  Definition t := nat.

  #[export] Instance dec : EqDecision t := Nat.eq_dec.
  #[export] Instance inf : Infinite t := nat_infinite.

  Definition default := 0.
End Atom.
#[export] Existing Instances Atom.dec Atom.inf.

Notation Name := Atom.t.

(* Finite set of names *)
Definition NameSet := (listset Name).