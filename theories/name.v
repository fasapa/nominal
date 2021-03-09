From stdpp Require Export prelude.
From stdpp Require Import listset countable infinite.

Module Type NAME.
  Parameter t: Set.
  Parameter eq_dec: EqDecision t.
  Parameter countable: @Countable t eq_dec.
  Parameter infinite: Infinite t.
  Parameter inhabited: Inhabited t.
End NAME.

Module Name: NAME.
  Definition t := nat.

  Instance eq_dec: EqDecision t := nat_eq_dec.
  Instance countable: @Countable t eq_dec := nat_countable.
  Instance infinite: Infinite t := nat_infinite.
  Instance inhabited: Inhabited t := nat_inhabited.
End Name.

Global Existing Instances
       Name.eq_dec Name.countable Name.infinite Name.inhabited.

Definition name := Name.t.
Definition nset := listset name.

Global Opaque name.
Global Opaque nset.

Declare Scope nominal_scope.
Delimit Scope nominal_scope with nominal.
