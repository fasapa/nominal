From Nominal Require Import Name Nominal Fresh.

#[export] Instance nat_action: PermAction nat := fun p n => n.
#[export] Instance nat_equiv: Equiv nat := eq.
#[export] Instance nat_support: Support nat := fun n => ∅.

#[export] Instance nat_perm: PermT nat.
Proof. 
    split; unfold equiv,nat_equiv,action,nat_action in *; repeat intro; auto.
    - typeclasses eauto.
Qed.

#[export] Instance nat_nominal: Nominal nat.
Proof. 
    split; intros.
    - apply nat_perm.
    - reflexivity.
Qed.

Lemma perm_nat: ∀ (p: Perm) (n: nat), p • n = n.
Proof. unfold action, nat_action; auto. Qed.