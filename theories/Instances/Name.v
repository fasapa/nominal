(* Name forms a nominal set *)
From Nominal Require Import Atom Nominal Fresh.

Instance name_action : PermAct name := swap_perm.
Instance name_equiv : Equiv name := eq.
Instance name_support : Support name := singleton.

Instance name_perm : Perm name.
Proof. 
    split; unfold "≡",name_equiv,action, prmact, name_action in *; repeat intro.
    - typeclasses eauto.
    - subst; rewrite H; auto.
    - auto.
    - symmetry; apply swap_perm_app.
Defined.

Instance name_nominal: Nominal name.
Proof. split; intros; [apply name_perm | apply swap_neither1; apply not_elem_of_singleton]; auto. Qed.

Lemma name_fresh_neq (a b: name): a # b → a ≠ b.
Proof. 
    intros [c [? cF]]; destruct (decide (a = c)); subst.
    - apply not_elem_of_singleton; auto.
    - apply swap_neither2 in cF as [[] | []]; subst; auto.
Qed.  

Lemma name_neq_fresh (a b: name): a ≠ b → a # b.
Proof. 
    intros; constructor 1 with a; split;
        [unfold support; apply not_elem_of_singleton | apply swap_neither1]; auto. 
Qed.

Lemma name_neq_fresh_iff (a b: name): a # b ↔ a ≠ b.
Proof. split; [apply name_fresh_neq | apply name_neq_fresh]. Qed.