From Nominal Require Export Prelude.
From stdpp Require Import listset countable infinite.

Module Type ATOMIC.
  Parameter t : Set.

  Axiom dec : EqDecision t.
  Axiom inf : Infinite t.
End ATOMIC.

Module Atom : ATOMIC.
  Definition t := nat.

  Instance dec : EqDecision t := nat_eq_dec.
  Instance inf : Infinite t := nat_infinite.
End Atom.
#[global] Existing Instances Atom.dec Atom.inf.

From elpi Require Import elpi.

(* Class Atomic A := { dec :> EqDecision A; inf :> Infinite A }.
Global Hint Mode Atomic ! : typeclass_instances.
Arguments dec {_ _} _ _ : simpl never, assert.
Arguments inf {_ _} : simpl never, assert.

Definition Name : Set := nat.
Instance name_atomic : Atomic Name. Proof. split; typeclasses eauto. Qed.

Arguments Name : simpl never, assert.
#[global] Opaque Name.
*)

Elpi Db atom.sort.db lp:{{
  pred atom-sort o:id.

  :name "atom.fail"
  atom-sort _ :- coq.error "NOMINAL-ERROR: No atom-sort defined.".
}}.

(* Define new atomic name *)
Elpi Command declare_name.
Elpi Accumulate Db atom.sort.db.
Elpi Accumulate declare_name lp:{{
  main [str X] :-
    coq.elpi.accumulate _ "atom.sort.db" (clause _ (before "atom.fail") (atom-sort X)),
    @global! => coq.notation.add-abbreviation X 0 {{ Atom.t }} ff _.

  main _ :- coq.say "Usage: declare_name [name]".
}}.
Elpi Typecheck.

Elpi declare_name name.

Notation nameset := (listset name).
