From Nominal Require Export PermT.

Class Support A := support: A → NameSet.
#[export] Hint Mode Support ! : typeclass_instances.
#[export] Instance: Params (@support) 1 := {}.

Class Nominal (X: Type) `{PrA: PermT X, Spt: Support X}: Prop :=
  support_spec: ∀ (x: X) (a b: Name),
    a ∉ (support x) → b ∉ (support x) → ⟨a,b⟩ • x ≡@{X} x.
