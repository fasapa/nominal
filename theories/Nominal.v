From Nominal Require Export PermT.

Class Support A := support: A → NameSet.
#[export] Hint Mode Support ! : typeclass_instances.
#[export] Instance: Params (@support) 1 := {}.

Section Nominal.
  Context (X: Type) `{PermT X}.

  Class Nominal `{Spt: Support X}: Prop := {
    nperm :> PermT X;
    support_spec: ∀ (x: X) (a b: Name),
      a ∉ (support x) → b ∉ (support x) → ⟨a,b⟩ • x ≡@{X} x
}.
End Nominal.
Arguments support_spec {_ PrA _ _ Nmn}: rename.
