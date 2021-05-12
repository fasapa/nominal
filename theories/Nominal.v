From Nominal Require Export Perm.

Class Support A := support: A → nameset.
#[global] Hint Mode Support ! : typeclass_instances.
Instance: Params (@support) 1 := {}.

Section Nominal.
  Context (X : Type) `{Perm X}.

  Class Nominal `{Spt : Support X}: Prop := {
    nperm :> Perm X;
    support_spec : ∀ (x: X) (a b: name),
        a ∉ (support x) → b ∉ (support x) → [(a,b)] • x ≡@{X} x
}.
End Nominal.
Arguments support_spec {_ PrA _ _ Nmn} : rename.

(* Freshness *)
Definition fresh_e `{Nominal X} (a: name) (x: X) :=
  ∃ (b : name), b ∉ support x ∧ ⟨a,b⟩ • x ≡@{X} x.

Definition fresh_a `{Nominal X} (a: name) (x: X) :=
  ∀ (b : name), b ∉ support x → ⟨a,b⟩ • x ≡ x.

(* Infix "#" := freshness (at level 50). *)
Infix "#ₑ" := fresh_e (at level 50).
Infix "#ₐ" := fresh_a (at level 50).

Lemma some_any `{Nominal X} (a: name) (x: X) : a #ₑ x ↔ a #ₐ x.
Proof.
  split.
  - intros [b [SB HH]] c SC; destruct (decide (c = a)), (decide (c = b)); subst; auto.
    + rewrite swap_equiv_neutral; apply gact_id.
    + rewrite swap_expand with (b := b); try rewrite <-2!gact_compat, HH, (support_spec _ b c); auto.
  - intros HH; exists (fresh (support x)); split.
    + apply is_fresh.
    + apply HH, is_fresh.
Qed.

Lemma support_fresh_e `{Nominal X} (a : name) (x: X):
  a ∉ support x → a #ₑ x.
Proof.
  intros; exists a; split; [idtac | rewrite swap_equiv_neutral; apply gact_id]; auto.
Qed.

Lemma support_fresh_a `{Nominal X} (a : name) (x: X): a ∉ support x → a #ₐ x.
Proof. intros; apply some_any, support_fresh_e; auto. Qed.
