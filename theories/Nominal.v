From Nominal Require Export Perm.

Class Support A := support: A → nameset.
#[global] Hint Mode Support ! : typeclass_instances.
Instance: Params (@support) 1 := {}.

Section Nominal.
  Context (X : Type) `{Perm X}.

  Class Nominal `{Spt : Support X}: Prop := {
    nperm :> Perm X;
    support_spec : ∀ (x: X) (a b: name),
        a ∉ (support x) → b ∉ (support x) → ⟨a,b⟩ • x ≡@{X} x
}.
End Nominal.
Arguments support_spec {_ PrA _ _ Nmn} : rename.