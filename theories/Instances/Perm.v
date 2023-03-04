(* Perm forms a nominal set *)
From Nominal Require Import Permutation Nominal.

#[export] Instance perm_action: PermAction Perm :=
    fun p' p => (-p') + (p + p').

#[export] Instance perm_support: Support Perm := perm_dom.

#[export] Instance perm_permt: PermT Perm.
Proof. Admitted.

#[export] Instance perm_nominal: Nominal Perm.
Proof. Admitted.
