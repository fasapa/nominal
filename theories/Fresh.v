From Nominal Require Import Nominal.

(* Record freshT `{Nominal X} (a: name) (x: X): Type := mkFreshT {
  new: name;
  new_fresh: new ∉ support x;
  new_fixpoint: ⟨a,new⟩ ∙ x ≡@{X} x
}. *)

Definition freshP_e `{Nominal X} (a: name) (x: X) := ∃ (b : name), b ∉ support x ∧ ⟨a,b⟩ ∙ x ≡@{X} x.
Definition freshP_a `{Nominal X} (a: name) (x: X) := ∀ (b : name), b ∉ support x → ⟨a,b⟩ ∙ x ≡@{X} x.

(* Infix "#" := freshT (at level 50). *)
(* Infix "#ₚₑ" := freshP_e (at level 50). *)
Infix "#" := freshP_e (at level 50).
Notation "(#)" := (freshP_e) (only parsing).
Notation "( a #)" := (freshP_e a) (only parsing).
Notation "a #( x , y )" := (a # x ∧ a # y) (at level 50).
Notation "a #( x , y , z )" := (a # x ∧ a # y ∧ a # z) (at level 50).
Notation "a #( x , y , z , w )" := (a # x ∧ a # y ∧ a # z ∧ a # w) (at level 50).
Infix "#ₐ" := freshP_a (at level 50).

Lemma some_any_iff `{Nominal X} (a: name) (x: X) : a # x ↔ a #ₐ x.
Proof.
  split.
  - intros [b [SB HH]] c SC; destruct (decide (c = a)), (decide (c = b)); subst; auto.
    + apply perm_action_equal.
    + rewrite perm_expand with (b := b); try rewrite <-2!gact_compat, HH, (support_spec _ b c); auto.
  - intros HH; exists (fresh (support x)); split.
    + apply is_fresh.
    + apply HH, is_fresh.
Qed.

(* Lemma fresh_spec_el `{Nominal X} (a: name) (x: X) : a # x → a #ₚₑ x.
Proof. intros [n ? ?]; exists n; split; auto. Qed. *)

(* Lemma fresh_spec_al `{Nominal X} (a: name) (x: X) : a # x → a #ₚₐ x.
Proof. intro; apply some_any, fresh_spec_el; auto. Qed. *)

(* Definition fresh_spec_ar `{Nominal X} (a: name) (x: X) : a #ₚₐ x → a # x.
Proof. 
  intros HH; constructor 1 with (fresh (support x)); pose proof (is_fresh (support x));
    specialize (HH (fresh (support x)) H1); auto.
Defined. *)

(* Definition fresh_spec_er `{Nominal X} (a: name) (x: X) : a #ₚₑ x → a # x.
Proof. intros HH; apply fresh_spec_ar, some_any; assumption. Defined. *)

Lemma support_fresh `{Nominal X} (a : name) (x: X): a ∉ support x → a # x.
Proof. intros; econstructor; split; [idtac | eapply perm_action_equal]; assumption. Qed.

(* Pode ser importante na frente *)
(* Definition update_fresh `{Nominal X} (a b: name) (x: X): a # x → b ∉ support x → a # x.
Proof. intros F ?; eapply fresh_spec_al in F; unfold freshP_a in F; econstructor; eauto. Defined.  *)

(* Lemma support_fresh_a `{Nominal X} (a : name) (x: X): a ∉ support x → a #ₐ x.
Proof. intros; apply some_any, support_fresh_e; auto. Qed. *)

Lemma fresh_support_fresh `{Nominal X} (x: X): fresh (support x) # x.
Proof. constructor 1 with (fresh (support x)); split; [apply is_fresh | apply perm_action_equal]. Qed.

Lemma fresh_fixpoint `{Nominal X} (a b : name) (x : X) : a # x → b # x → ⟨a,b⟩ ∙ x ≡ x.
Proof.
  intros FA FB; destruct (decide (a = b)); subst.
  - apply perm_action_equal.
  - destruct FA as [p [? Fp]]; destruct FB as [k [? Fk]];
      destruct (decide (p = k)), (decide (k = a)), (decide (k = b)), 
        (decide (p = a)), (decide (p = b)); subst;
          try first [assumption | apply perm_action_equal | rewrite perm_swap; assumption]. 
    + rewrite (perm_expand _ k _), <-!gact_compat, Fp, (perm_swap k b), Fk; auto; apply Fp.
    + apply support_spec; auto. 
    + rewrite (perm_expand _ p _), <-!gact_compat, Fp, (support_spec _ p b); auto.
    + rewrite (perm_expand _ k _), <-!gact_compat, (support_spec x a k), (perm_swap k b), 
        Fk, support_spec; auto. 
    + rewrite (perm_expand _ p _), (perm_expand p k b), !grp_assoc, <-!gact_compat, 
        Fp, (perm_swap k b), (support_spec x p k), Fk, (support_spec x p k), Fp; auto.
Qed.

(* Fresh tactics *)
Ltac support_fresh_tac :=
  repeat (match goal with
    | [H : _ ∉ support _ |- _] => apply support_fresh in H
    end).
Ltac destruct_notin_union :=
    repeat (match goal with 
      | [H : _ ∉ _ ∪ _ |- _] => apply not_elem_of_union in H as []
      end).

Tactic Notation "new" ident(w) "fresh" constr(H1) :=
destruct (exist_fresh (support H1)) as [w ?]; 
destruct_notin_union; support_fresh_tac.

Tactic Notation "new" ident(w) "fresh" constr(H1) constr(H2) :=
destruct (exist_fresh (support H1 ∪ support H2)) as [w ?]; 
destruct_notin_union; support_fresh_tac.

Tactic Notation "new" ident(w) "fresh" constr(H1) constr(H2) constr(H3) :=
destruct (exist_fresh (support H1 ∪ support H2 ∪ support H3)) as [w ?]; 
destruct_notin_union; support_fresh_tac.

Tactic Notation "new" ident(w) "fresh" constr(H1) constr(H2) constr(H3) constr(H4) :=
destruct (exist_fresh (support H1 ∪ support H2 ∪ support H3 ∪ support H4)) as [w ?];
destruct_notin_union; support_fresh_tac.

Tactic Notation "new" ident(w) "fresh" constr(H1) constr(H2) constr(H3) constr(H4) constr(H5) :=
destruct (exist_fresh (support H1 ∪ support H2 ∪ support H3 ∪ support H4 ∪ support H5)) as [w ?];
destruct_notin_union; support_fresh_tac.

Tactic Notation "new" ident(w) "fresh" constr(H1) constr(H2) constr(H3) constr(H4) constr(H5) constr(H6) :=
destruct (exist_fresh (support H1 ∪ support H2 ∪ support H3 ∪ support H4 ∪ support H5 ∪ support H6)) as [w ?];
destruct_notin_union; support_fresh_tac.

Tactic Notation "new" ident(w) "fresh" constr(H1) constr(H2) constr(H3) constr(H4) constr(H5) constr(H6) constr(H7) constr(H8) :=
destruct (exist_fresh (support H1 ∪ support H2 ∪ support H3 ∪ support H4 ∪ support H5 ∪ support H6 ∪ support H7 ∪ support H8)) as [w ?];
destruct_notin_union; support_fresh_tac.

(* Name and freshness *)
From Nominal Require Import Instances.Name.

Instance fresh_proper `{Nominal X}: Proper ((≡@{name}) ⟹ (≡@{X}) ⟹ flip impl) (#).
Proof.
  intros a b HeqN x y HeqX; destruct (exist_fresh (support a ∪ support x ∪ support y)) as [w ?]; exists w; split;
  [| apply some_any_iff in H2; rewrite HeqN, HeqX; apply H2]; destruct_notin_union; auto.
Qed.

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

(* Freshness properties *)
Lemma fresh_equivariant `{Nominal X} p a (x: X): a # x → (p ∙ a) # (p ∙ x).
Proof.
  intro F; destruct (exist_fresh (support p ∪ support x ∪ support (p ∙ x))) as [w ?]; exists w;
    split; [set_solver |]; cut (w ≡ p ∙ w); [intro HH | rewrite perm_notin_domain_id; set_solver]; 
    rewrite HH,gact_compat,<-perm_comm_distr,<-gact_compat,fresh_fixpoint; auto.
    destruct_notin_union; support_fresh_tac; auto.
Qed.

From Nominal Require Import Instances.Prod.

Lemma fresh_pair_iff `{Nominal X} (a b: name) (x: X): a # (b, x) ↔ a ≠ b ∧ a # x.
Proof.
  split; [intros [w [? Hf]] | intros []].
    - unfold support,prod_support,action,prod_act,equiv,prod_equiv,prod_relation in *; simpl in *.
      destruct Hf as [Hf1 Hf2]; split.
      + unfold action, name_action in *; simpl in *; try repeat case_decide; subst; destruct_notin_union.
        * support_fresh_tac; try apply name_fresh_neq in H1; congruence.
        * exfalso; apply H1; set_solver.
        * assumption.
      + exists w; split; auto; destruct_notin_union; auto.
    - destruct (exist_fresh (support a ∪ support b ∪ support x ∪ support (b, x))) as [w ?]; exists w; split.
      + destruct_notin_union; set_solver.
      + unfold action,equiv,prod_act,prod_equiv,prod_relation; split; simpl; apply fresh_fixpoint; auto; 
        destruct_notin_union; support_fresh_tac; [apply name_neq_fresh_iff | |]; auto.
Qed.