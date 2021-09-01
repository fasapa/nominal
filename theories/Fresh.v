From Nominal Require Import Nominal.

(* Freshness *)
Definition fresh_e `{Nominal X} (a: name) (x: X) :=
  ∃ (b : name), b ∉ support x ∧ ⟨a,b⟩ • x ≡@{X} x.

Definition fresh_a `{Nominal X} (a: name) (x: X) :=
  ∀ (b : name), b ∉ support x → ⟨a,b⟩ • x ≡ x.

(* Infix "#" := freshness (at level 50). *)
Infix "#ₑ" := fresh_e (at level 50).
Infix "#ₐ" := fresh_a (at level 50).

(* Lemma some_any `{Nominal X} (a b : name) (x : X) : 
  b ∉ support x → ⟨a,b⟩ • x ≡@{X} x → (∀ c, c ∉ support x → ⟨a,c⟩ • x ≡@{X} x).
Proof.
  intros; destruct (decide (c = a)), (decide (c = b)); subst; auto.
  - apply perm_action_equal.
  - rewrite perm_expand with (b := b); 
      try rewrite <-2!gact_compat, H2, (support_spec _ b c); auto.
Qed. *)

Lemma some_any `{Nominal X} (a: name) (x: X) : a #ₑ x ↔ a #ₐ x.
Proof.
  split.
  - intros [b [SB HH]] c SC; destruct (decide (c = a)), (decide (c = b)); subst; auto.
    + apply perm_action_equal.
    + rewrite perm_expand with (b := b); try rewrite <-2!gact_compat, HH, (support_spec _ b c); auto.
  - intros HH; exists (fresh (support x)); split.
    + apply is_fresh.
    + apply HH, is_fresh.
Qed.

Lemma support_fresh_e `{Nominal X} (a : name) (x: X):
  a ∉ support x → a #ₑ x.
Proof.
  intros; exists a; split; [idtac | apply perm_action_equal]; auto.
Qed.

Lemma support_fresh_a `{Nominal X} (a : name) (x: X): a ∉ support x → a #ₐ x.
Proof. intros; apply some_any, support_fresh_e; auto. Qed.

Lemma fresh_support_fresh `{Nominal X} (x: X): fresh (support x) #ₑ x.
Proof. unfold fresh_e; exists (fresh (support x)); split;
        [apply is_fresh | apply perm_action_equal].
Qed.