From Nominal Require Export Perm.

Class Support A := support: A → nameset.
#[global] Hint Mode Support ! : typeclass_instances.
Instance: Params (@support) 1 := {}.

Section Nominal.
  Context (X: Type) `{Perm X}.

  Class Nominal `{Spt: Support X}: Prop := {
    nperm :> Perm X;
    support_spec: ∀ (x: X) (a b: name),
      a ∉ (support x) → b ∉ (support x) → ⟨a,b⟩ ∙ x ≡@{X} x
}.
End Nominal.
Arguments support_spec {_ PrA _ _ Nmn} : rename.

(* Section NominalProperties.
  Context `{Nominal X} (a b c : name) (x : X).
  
  Lemma lala : (a ∉ support x) → (c ∉ support x) →
    a ≠ b → b ≠ c →
    ⟨ c, a ⟩ ∙ ⟨ a, b ⟩ ∙ x ≡ ⟨ c, b ⟩ ∙ x.
  Proof.
    intros; rewrite (perm_expand c a b).
    + repeat rewrite <- gact_compat. rewrite (support_spec x c a). auto.
    + auto.
    + auto.
  Qed.
        
End NominalProperties. *)
