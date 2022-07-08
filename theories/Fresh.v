From Nominal Require Import Nominal.

(* Record freshT `{Nominal X} (a: name) (x: X): Type := mkFreshT {
  new: name;
  new_fresh: new ∉ support x;
  new_fixpoint: ⟨a,new⟩ • x ≡@{X} x
}. *)

Definition freshP_e `{Nominal X} (a: name) (x: X) := ∃ (b: name), b ∉ (support x) ∧ ⟨a,b⟩ • x ≡@{X} x.
Definition freshP_a `{Nominal X} (a: name) (x: X) := ∀ (b: name), b ∉ support x → ⟨a,b⟩ • x ≡@{X} x.

(* Infix "#" := freshT (at level 50). *)
(* Infix "#ₚₑ" := freshP_e (at level 50). *)
Infix "#" := freshP_e (at level 50).
Notation "(#)" := (freshP_e) (only parsing).
Notation "( a #)" := (freshP_e a) (only parsing).
Notation "a #[ x , y ]" := (a # x ∧ a # y) (at level 50).
Notation "a #[ x , y , z ]" := (a # x ∧ a # y ∧ a # z) (at level 50).
Notation "a #[ x , y , z , w ]" := (a # x ∧ a # y ∧ a # z ∧ a # w) (at level 50).
Infix "#ₐ" := freshP_a (at level 50).

Lemma support_fresh `{Nominal X} (a : name) (x: X): a ∉ support x → a # x.
Proof. intros; econstructor; split; [idtac | eapply perm_action_equal]; assumption. Qed.

(* Freshness Tactics *)
Ltac fresh_tac :=
  repeat (match goal with
    | [H : _ ∉ _ ∪ _ |- _] => apply not_elem_of_union in H as []
    | [H : _ ∉ support _ |- _ # _] => apply support_fresh in H
    | [H : _ ∉ support _ |- _] => apply support_fresh in H
    end; auto).

Tactic Notation "new" ident(w) "fresh" constr(H1) :=
destruct (exist_fresh (support H1)) as [w ?]; 
fresh_tac.

Tactic Notation "new" ident(w) "fresh" constr(H1) constr(H2) :=
destruct (exist_fresh (support H1 ∪ support H2)) as [w ?]; 
fresh_tac.

Tactic Notation "new" ident(w) "fresh" constr(H1) constr(H2) constr(H3) :=
destruct (exist_fresh (support H1 ∪ support H2 ∪ support H3)) as [w ?]; 
fresh_tac.

Tactic Notation "new" ident(w) "fresh" constr(H1) constr(H2) constr(H3) constr(H4) :=
destruct (exist_fresh (support H1 ∪ support H2 ∪ support H3 ∪ support H4)) as [w ?];
fresh_tac.

Tactic Notation "new" ident(w) "fresh" constr(H1) constr(H2) constr(H3) constr(H4) constr(H5) :=
destruct (exist_fresh (support H1 ∪ support H2 ∪ support H3 ∪ support H4 ∪ support H5)) as [w ?];
fresh_tac.

Tactic Notation "new" ident(w) "fresh" constr(H1) constr(H2) constr(H3) constr(H4) constr(H5) constr(H6) :=
destruct (exist_fresh (support H1 ∪ support H2 ∪ support H3 ∪ support H4 ∪ support H5 ∪ support H6)) as [w ?];
fresh_tac.

Tactic Notation "new" ident(w) "fresh" constr(H1) constr(H2) constr(H3) constr(H4) constr(H5) constr(H6) constr(H7) constr(H8) :=
destruct (exist_fresh (support H1 ∪ support H2 ∪ support H3 ∪ support H4 ∪ support H5 ∪ support H6 ∪ support H7 ∪ support H8)) as [w ?];
fresh_tac.

Tactic Notation "new" ident(w) "fresh" constr(H1) constr(H2) constr(H3) constr(H4) constr(H5) constr(H6) constr(H7) constr(H8) constr(H9) :=
destruct (exist_fresh (support H1 ∪ support H2 ∪ support H3 ∪ support H4 ∪ support H5 ∪ support H6 ∪ support H7 ∪ support H8 ∪ support H9)) as [w ?];
fresh_tac.

Tactic Notation "new" ident(w) "fresh" constr(H1) constr(H2) constr(H3) constr(H4) constr(H5) constr(H6) constr(H7) constr(H8) constr(H9) constr(H10) :=
destruct (exist_fresh (support H1 ∪ support H2 ∪ support H3 ∪ support H4 ∪ support H5 ∪ support H6 ∪ support H7 ∪ support H8 ∪ support H9 ∪ support H10)) as [w ?];
fresh_tac.

(* Freshness properties *)
Lemma some_any_iff `{Nominal X} (a: name) (x: X): a # x ↔ a #ₐ x.
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

(* Pode ser importante na frente *)
(* Definition update_fresh `{Nominal X} (a b: name) (x: X): a # x → b ∉ support x → a # x.
Proof. intros F ?; eapply fresh_spec_al in F; unfold freshP_a in F; econstructor; eauto. Defined.  *)

(* Lemma support_fresh_a `{Nominal X} (a : name) (x: X): a ∉ support x → a #ₐ x.
Proof. intros; apply some_any, support_fresh_e; auto. Qed. *)

Lemma fresh_support_fresh `{Nominal X} (x: X): fresh (support x) # x.
Proof. constructor 1 with (fresh (support x)); split; [apply is_fresh | apply perm_action_equal]. Qed.

Lemma fresh_eq `{Nominal X} (a: name) (x x': X): x ≡ x' → a # x → a # x'.
Proof. 
    intros E F; destruct (exist_fresh (support x ∪ support x')) as [w ?]; exists w; split;
    [| apply some_any_iff in F; rewrite <-E; apply F]; fresh_tac.
Qed.

(* ≡@{name} <=> eq (=) *)
#[export] Instance fresh_proper1 `{Nominal X}: Proper (eq ⟹ (≡@{X}) ⟹ impl) (#).
Proof. repeat intro; subst; eapply fresh_eq; eauto. Qed.

(* ≡@{name} <=> eq (=) *)
#[export] Instance fresh_proper2 `{Nominal X}: Proper (eq ⟹ (≡@{X}) ⟹ flip impl) (#).
Proof. 
  intros a b HeqN x y HeqX; destruct (exist_fresh (singleton a ∪ support x ∪ support y)) as [w ?]; exists w; split;
  [| apply some_any_iff in H2; rewrite HeqN, HeqX; apply H2]; fresh_tac.
Qed.

Lemma fresh_fixpoint `{Nominal X} (a b: name) (x : X): a # x → b # x → ⟨a,b⟩ • x ≡ x.
Proof.
  intros FA FB; destruct (decide (a = b)); subst.
  - apply perm_action_equal.
  - destruct FA as [p [? Fp]]; destruct FB as [k [? Fk]];
      destruct (decide (p = k)), (decide (k = a)), (decide (k = b)), 
        (decide (p = a)), (decide (p = b)); subst;
          try first [assumption | apply perm_action_equal | rewrite swap_perm; assumption]. 
    + rewrite (perm_expand _ k _), <-!gact_compat, Fp, (swap_perm k b), Fk; auto; apply Fp.
    + apply support_spec; auto. 
    + rewrite (perm_expand _ p _), <-!gact_compat, Fp, (support_spec _ p b); auto.
    + rewrite (perm_expand _ k _), <-!gact_compat, (support_spec x a k), (swap_perm k b), 
        Fk, support_spec; auto. 
    + rewrite (perm_expand _ p _), (perm_expand p k b), !grp_assoc, <-!gact_compat, 
        Fp, (support_spec x p k), (swap_perm k b), Fk, (support_spec x p k), Fp; auto.
Qed.

Lemma fresh_equivariant `{Nominal X} (p: perm) (a: name) (x: X): a # x → (perm_swap p a) # (p • x).
Proof.
  intro F; destruct (exist_fresh (perm_dom p ∪ support x ∪ support (p • x))) as [w ?]; exists w;
    split; [set_solver |]; cut (w = perm_swap p w); [intro HH | rewrite perm_notin_domain_id; set_solver]; 
    rewrite HH,gact_compat,<-perm_comm_distr,<-gact_compat,fresh_fixpoint; auto.
    fresh_tac; assumption.
Qed.