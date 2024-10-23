From Nominal Require Import Nominal Fresh NameAbstraction.
From Nominal.Instances Require Import SupportedFunctions Name.

Section FT.

Context `{Nominal X} (h: Name →ₛ X) (Hp: ∃ a, a # h ∧ a # (h a)).
  
Definition freshF: X := h (fresh (support h)).

Lemma freshness_theorem_some_any: (∃ a, a # h ∧ a # (h a)) ↔ (∀ a, a # h → a # (h a)).
Proof.
  split; intros HH.
  - intros a AH; destruct HH as [b [BH1 BH2]]; destruct (decide (a = b)).
    + subst; assumption.
    + apply (fresh_equivariant ⟨a,b⟩) in BH2; 
      rewrite perm_swap_right,fun_equivar,perm_swap_right,fresh_fixpoint in BH2; assumption.
  - new c fresh h; exists c; split.
    + apply support_fresh; assumption.
    + apply HH, support_fresh; assumption.
Qed.

Theorem freshness_theorem: ∀ a, a # h → (h a) ≡ freshF.
Proof.
  intros a AH; unfold freshF; set (a' := fresh _); destruct (decide (a = a')); subst; try reflexivity.
  rewrite <-(fresh_fixpoint a a' (h a')), fun_equivar,perm_swap_right,fresh_fixpoint.
    + reflexivity.
    + assumption.
    + apply fresh_support_fresh.
    + apply fresh_fun_supp; [| apply name_neq_fresh_iff]; assumption.
    + apply freshness_theorem_some_any; [| apply fresh_support_fresh]; apply Hp.
Qed.

Corollary freshness_theorem_inj: ∀ a b, a # h → b # h → h a ≡ h b.
Proof. 
  intros; rewrite !freshness_theorem; try reflexivity; try assumption;
  destruct H1 as [x ?]; exists x; split; try (apply support_fresh; tauto); tauto.
Qed.

End FT.