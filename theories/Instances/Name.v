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

(* FIXME: Por aonde? *)
Instance perm_support: Support perm := λ p, perm_dom p.

Lemma name_fresh_action p (a b: name): b # a → b ∉ perm_dom p → b # (p ∙ a).
Proof.
    intros HH ?; destruct (exist_fresh (support a ∪ support b ∪ support p ∪ support (p ∙ a))) as [w ?];
    exists w; split; [set_solver |]; 
    rewrite gact_compat, <-perm_notin_dom_comm, <-gact_compat; [| set_solver | set_solver].
    apply some_any_iff in HH; cut (w ∉ support a); [intros HHH | set_solver]; 
    specialize (HH w HHH); rewrite HH; reflexivity.
Qed.