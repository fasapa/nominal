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