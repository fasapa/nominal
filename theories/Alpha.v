From Nominal Require Import Nominal Fresh.

(* Instance alpha_equiv `{Nominal X} : Equiv (name * X) :=
    λ '(a1, x1) '(a2, x2), ∃ (b : name), b # x1 ∧ b # x2 ∧ ⟨b,a1⟩ • x1 ≡@{X} ⟨b,a2⟩ • x2.
    
Infix "≈α" := (alpha_equiv) (at level 70, no associativity).

Section AlphaEquivalence.
    Context `{Nominal X}.

    Lemma alpha_equiv_forall `{Nominal X} a1 a2 x1 x2 :
        (a1, x1) ≈α (a2, x2) → (∀ c, c #ₑ x1 ∧ c #ₑ x2 → ⟨c,a1⟩ • x1 ≡@{X} ⟨c,a2⟩ • x2).
    Proof.
        intros [b Hb] c Hc; destruct_and!; destruct (decide (b = c)); subst.
        - assumption.
        - destruct H5 as [x []].
        
        
        
        
        
        
        destruct (decide (b = a1)), (decide (b = a2)), (decide (c = a1)), (decide (c = a2));
            try congruence; subst; try (rewrite perm_equiv_neutral in );
            repeat match goal with
            | H : context[ɛ • _] |- _ => rewrite gact_id in H
            | _ : _ |- context[ɛ • _] => rewrite gact_id
            end.
            + rewrite H8; auto.
            + rewrite H8; rewrite perm_swap; apply perm_action_duplicate.
            + rewrite (perm_expand c a1 a2); auto;
                repeat rewrite <-gact_compat; rewrite (support_spec x2); auto;
                rewrite <-H8; reflexivity.
            + rewrite support_spec in H8; auto; rewrite H8; symmetry; apply support_spec; auto.
            + rewrite (perm_expand _ a2 _); auto; repeat rewrite <-gact_compat; 
                rewrite (support_spec x1); auto; rewrite H8; reflexivity.
            + eapply perm_inj; eauto.
            + rewrite support_spec in H8; auto; rewrite (perm_expand _ b _); auto;
                repeat rewrite <-gact_compat; rewrite (support_spec x2 _ _); auto;
                rewrite <-H8; rewrite support_spec; auto.
            + rewrite (support_spec x2) in H8; auto; rewrite (perm_expand _ b _); auto;
                repeat rewrite <-gact_compat; rewrite (support_spec x1 _ _); auto;
                rewrite H8; rewrite support_spec; auto.
            + apply (perm_inj) with ⟨b, c⟩; rewrite <-(support_spec x1 b c); eauto.
                rewrite <-(support_spec x2 b c); eauto; repeat rewrite gact_compat;
                repeat rewrite grp_assoc. rewrite <-2!perm_expand; auto.
    Qed.               

    (* #[global] Instance alpha_equiv_a `{Nominal X} : Equiv (name * X) :=
        λ '(a1, x1) '(a2, x2), ∃ (a : name), a #ₑ x1 ∧ a #ₑ x2 ∧ ⟨a,a1⟩ • x1 ≡@{X} ⟨a,a2⟩ • x2.
    
    Infix "≈αₑ" := (alpha_equiv_e) (at level 70, only parsing, no associativity). *)

    #[global] Instance alpha_equivalence: Equivalence alpha_equiv.
    Proof.
        split; repeat intro;
        repeat match goal with p : name * X |- _ => destruct p end.
        - exists (fresh (support x)); repeat try split; auto; apply is_fresh.
        - destruct H1; exists x1; intuition.
        - set (S := (support x) ∪ (support x1) ∪ (support x0));
            pose proof (is_fresh S); exists (fresh S); repeat split; [set_solver | set_solver |].
            eapply alpha_equiv_forall with (c := fresh S) in H1,H2; [| set_solver | set_solver].
            rewrite H1, H2; auto.
    Qed.   
End AlphaEquivalence.

Section AlphaEquivalenceProperties.
    Context `{Nominal X} (a1 a2 : name) (x1 x2 : X).

    Lemma alpha_inv1: (a1, x1) ≈α (a2, x2) → a1 = a2 → x1 ≡ x2.
    Proof. intros [? [? []]] ?; subst; eapply perm_inj; eauto. Qed.

    Lemma alpha_inv2: a1 = a2 → x1 ≡ x2 → (a1, x1) ≈α (a2, x2).
    Proof. intros ? HX; subst; set (S := (support x1) ∪ (support x2)); 
        exists (fresh S); repeat try split.
        - apply is_fresh_union_left.
        - apply is_fresh_union_right.
        - apply perm_inj; auto.
    Qed.

    Lemma alpha_inv_fresh: (a1, x1) ≈α (a2, x2) → a1 #ₑ x1 → a2 #ₑ x2 → x1 ≡ x2.
    Proof. intros. eapply alpha_equiv_forall in H1.
    
    intros [b [? []]] ? ?.

End AlphaEquivalenceProperties. *)
