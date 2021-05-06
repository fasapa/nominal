From Nominal Require Export Perm.

Class Support A := support: A -> nameset.
#[global] Hint Mode Support ! : typeclass_instances.

Section Nominal.
  Context X `{PX: Perm X, S: Support X}.

  Class Nominal: Prop := {
    nom_perm :> Perm X;
    support_spec : forall (x: X) (a b: name),
        a ∉ (support x) -> b ∉ (support x) -> [(a,b)] • x ≡@{X} x
}.
End Nominal.

#[global] Hint Mode Nominal ! - - - : typeclass_instances.
Arguments support_spec {X XPAct XEq XS XN}: rename.

(* Freshness *)
Definition fresh_e `{Nominal X} (a: Name) (x: X) :=
  exists b, b ∉ support x /\ [(a,b)] • x ≡ x.

Definition fresh_a `{Nominal X} (a: Name) (x: X) :=
  forall b, b ∉ support x -> [(a,b)] • x ≡ x.

(* Infix "#" := freshness (at level 50). *)
Infix "#ₑ" := fresh_e (at level 50).
Infix "#ₐ" := fresh_a (at level 50).

Lemma some_any `{Nominal X} (a: Name) (x: X) : a #ₑ x <-> a #ₐ x.
Proof.
  split.
  - intros [b [SB HH]] c SC; destruct (decide (c = a)), (decide (c = b)); subst; auto.
    + rewrite swap_equiv_neutral; apply gact_id.
    + rewrite swap_expand with (b := b); try rewrite <-2!gact_compat, HH, (support_spec _ b c); auto.
  - intros HH; exists (fresh (support x)); split.
    + apply is_fresh.
    + apply HH, is_fresh.
Qed.

Lemma support_fresh_e `{Nominal X} a (x: X):
  a ∉ support x -> a #ₑ x.
Proof.
  intros; exists a; split; [idtac | rewrite swap_equiv_neutral; apply action_id]; auto.
Qed.

Lemma support_fresh_a `{Nominal X} a (x: X): a ∉ support x -> a #ₐ x.
Proof. intros; apply some_any, support_fresh_e; auto. Qed.
