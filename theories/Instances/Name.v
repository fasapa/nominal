(* Name forms a nominal set *)
From Nominal Require Import Atom Nominal.

#[export] Instance name_action: PermAction name := swap_perm.
#[export] Instance name_equiv: Equiv name := eq.
#[export] Instance name_support: Support name := (singleton (A := name) (B := nameset)).

#[export] Instance name_perm: Perm name.
Proof. 
    split; unfold "≡", name_equiv,action,name_action in *; repeat intro.
    - typeclasses eauto.
    - subst; rewrite H; auto.
    - auto.
    - symmetry; apply swap_perm_app.
Defined.

#[export] Instance name_nominal: Nominal name.
Proof. split; intros; [apply name_perm | apply swap_neither1; apply (not_elem_of_singleton (C := nameset))]; auto. Qed.