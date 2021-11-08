Require Import Coq.Classes.RelationClasses.
From Nominal Require Import Nominal Fresh Instances.Name.

(* Record NameAbstraction `{Nominal X} (a1x1 a2x2: name * X) := mkNameAbstraction {
    new: name;
    new_fresh1: new # (snd a1x1);
    new_fresh2: new # (snd a2x2);
    new_fixpoint: ⟨new, fst a1x1⟩ • (snd a1x1) ≡@{X} ⟨new, fst a2x2⟩ • (snd a2x2) 
}. *)

Definition NameAbstraction_e `{Nominal X} (a1x1 a2x2: name * X) :=
    ∃ (b: name), b #(fst a1x1, fst a2x2, snd a1x1, snd a2x2) ∧ 
                 ⟨b,fst a1x1⟩ • (snd a1x1) ≡@{X} ⟨b,fst a2x2⟩ • (snd a2x2).

Definition NameAbstraction_a `{Nominal X} (a1x1 a2x2: name * X) :=
    ∀ (b: name), b #(fst a1x1, fst a2x2, snd a1x1, snd a2x2) →
                 ⟨b,fst a1x1⟩ • (snd a1x1) ≡@{X} ⟨b,fst a2x2⟩ • (snd a2x2).

Instance alpha_equiv_e `{Nominal X}: Equiv (name * X) | 0 := NameAbstraction_e.
Instance alpha_equiv_a `{Nominal X}: Equiv (name * X) | 1 := NameAbstraction_a.
    
Infix "≈α" := (alpha_equiv_e) (at level 70, no associativity).
Infix "≈αₐ" := (alpha_equiv_a) (at level 70, no associativity).

Section AlphaEquivalence.
    Context `{Nominal X}.

    Lemma alpha_equiv_some_any `{Nominal X} a1 a2 x1 x2 :
        (a1, x1) ≈α (a2, x2) ↔ (a1, x1) ≈αₐ (a2, x2).
    Proof.
        split; intros Hα; unfold alpha_equiv_e, alpha_equiv_a, NameAbstraction_e, NameAbstraction_a in *;
            simpl in *.
        - intros; simpl in *; destruct Hα as [y [? Hα]]; destruct_and!;
            rewrite (perm_expand _ y a1), (perm_expand _ y a2), <-!gact_compat, 
                (fresh_fixpoint _ _ x1), (fresh_fixpoint _ _ x2), Hα;
                    try (apply not_eq_sym, name_neq_fresh_iff); auto.
        - new b fresh a1 a2 x1 x2; exists b; split; [ | apply Hα]; intuition.
    Qed.

    #[global] Instance alpha_equivalence_e: Equivalence alpha_equiv_e.
    Proof.
        split.
        - intros [a x]; destruct (exist_fresh (support a ∪ support x)) as [y []%not_elem_of_union];
            exists y; split_and!; simpl; try (apply support_fresh); auto.
        - intros ? ? [z ?]; exists z; intuition. 
        - intros [a x] [b y] [c z] ? ?; simpl in *.
            new f fresh a x b y c z; apply alpha_equiv_some_any in H1,H2; exists f; split; simpl;
                [| rewrite (H1 f), (H2 f)]; intuition. 
    Qed.

    #[global] Instance alpha_equivalence_a: Equivalence alpha_equiv_a.
    Proof.
        split.
        - intros [] ? ?; simpl; reflexivity.
        - intros [] [] HH b ?; specialize (HH b); intuition.
        - intros [] [q p] [] H1 H2; apply alpha_equiv_some_any in H1,H2; apply alpha_equiv_some_any.
            (* for some reason Coq cant find an instance for Transitive alpha_equiv_e, even though its
               define just above. *)
            pose proof (@Equivalence_Transitive _ _ alpha_equivalence_e).
            transitivity (q, p); auto.
    Qed.
End AlphaEquivalence.

Section AlphaEquivalenceProperties.
    Context `{Nominal X} (a1 a2 : name) (x1 x2 : X).

    Lemma alpha_inv1: (a1, x1) ≈α (a2, x2) → a1 = a2 → x1 ≡ x2.
    Proof. intros [? [? ?]] ?; subst; eapply perm_inj; eauto. Qed.

    Lemma alpha_inv2: a1 = a2 → x1 ≡ x2 → (a1, x1) ≈α (a2, x2).
    Proof. 
        intros ? HX; subst; new w fresh x1 x2 a2; exists w; simpl; split; [| rewrite HX]; intuition.
    Qed.

    Lemma alpha_inv_fresh: (a1, x1) ≈α (a2, x2) → a1 # x1 → a2 # x2 → x1 ≡ x2.
    Proof.
        intros A%alpha_equiv_some_any F1 F2; new w fresh a1 a2 x1 x2;
        cut (w #( a1, a2, x1, x2)); [intros FF | set_solver];
        specialize (A w FF); simpl in *; rewrite 2!fresh_fixpoint in A; auto.
    Qed.

End AlphaEquivalenceProperties.