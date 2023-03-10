(* Name forms a nominal set *)
From Nominal Require Import Name Nominal Fresh.

#[export] Instance name_action: PermAction Name := perm_swap.
#[export] Instance name_equiv: Equiv Name := eq.
#[export] Instance name_support: Support Name := (singleton (A := Name) (B := NameSet)).

#[export] Instance name_perm: PermT Name.
Proof. 
    split; unfold equiv,name_equiv,action,name_action in *; repeat intro.
    - typeclasses eauto.
    - subst; rewrite H; auto.
    - auto.
    - symmetry; apply perm_swap_app.
Qed.

#[export] Instance name_nominal: Nominal Name.
Proof. 
    split; intros; 
        [apply name_perm | 
         apply swap_neither1; apply (not_elem_of_singleton (C := NameSet))]; 
    auto.
Qed.

(* Freshness properties for name *)
Lemma name_fresh_neq1 (a b: Name): a # b → a ≠ b.
Proof. 
    intros [c [? cF]]; destruct (decide (a = c)); subst.
    - apply (not_elem_of_singleton (C := NameSet)); auto.
    - apply swap_neither2 in cF as [[] | []]; subst; auto.
Qed.  

Lemma name_fresh_neq2 (a b: Name): a ≠ b → a # b.
Proof. 
    intros; constructor 1 with a; split;
        [unfold support; apply not_elem_of_singleton | apply swap_neither1]; auto. 
Qed.

Lemma name_neq_fresh_iff (a b: Name): a # b ↔ a ≠ b.
Proof. split; [apply name_fresh_neq1 | apply name_fresh_neq2]. Qed.

Lemma name_fresh_iff (a b: Name): a # b ↔ b # a.
Proof. 
    split; intro H; apply name_neq_fresh_iff in H; apply name_neq_fresh_iff;
    apply not_eq_sym; assumption.
Qed.

Lemma name_fresh_action p (a b: Name): b # a → b ∉ perm_dom p → b # (p • a).
Proof.
    intros HH ?; destruct (exist_fresh (support a ∪ support b ∪ perm_dom p ∪ support (p • a))) as [w ?];
    exists w; split; [set_solver |]; 
    rewrite gact_compat, <-perm_notin_dom_comm, <-gact_compat; [| set_solver | set_solver].
    apply some_any_iff in HH; cut (w ∉ support a); [intros HHH | set_solver]; 
    specialize (HH w HHH); rewrite HH; reflexivity.
Qed.

Lemma name_fresh_false (a: Name): not (a # a).
Proof.
    intros [? [H1 H2]]; unfold support, name_support in *; apply not_elem_of_singleton_1 in H1.
    rewrite perm_swap_left in H2; congruence.
Qed.

Lemma name_action_left (a b: Name) : ⟨a,b⟩ • a ≡ b.
Proof. unfold action, name_action; apply perm_swap_left. Qed.

Lemma name_action_right (a b: Name) : ⟨a,b⟩ • b ≡ a.
Proof. unfold action, name_action; apply perm_swap_right. Qed.

Lemma nameset_fresh_respect (A B: NameSet): A ≡ B → fresh A ≡ fresh B.
Proof. intros AB; rewrite AB; reflexivity. Qed.