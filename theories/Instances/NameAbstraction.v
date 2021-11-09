From Nominal Require Import Alpha Instances.Name Instances.Prod.

(* Notation " '[𝔸]' X " := (name * X)%type (at level 70, no associativity). *)

Section NameAbstractionNominal.
    Context `{Nominal X}.

    Definition name_abs := (name * X)%type.
 
    #[global] Instance name_abstraction_equiv: Equiv name_abs := (≈α).
    #[global] Instance name_abstraction_equivalence: Equivalence name_abstraction_equiv.
    Proof. exact alpha_equivalence_e. Qed.

    #[global] Instance name_abstraction_action: PermAct name_abs := prod_act. 
    #[global] Instance name_abstraction_perm: Perm name_abs.
    Proof.
        split.
        - exact name_abstraction_equivalence.
        - intros p q Heq1 [a x] [b x'] Heq2; 
            unfold action, prmact, name_abstraction_action, prod_act;
            unfold equiv, name_abstraction_equiv; unfold equiv, name_abstraction_equiv in Heq2.
            new w fresh p q a b x x' (p ∙ x) (q ∙ x'); apply alpha_equiv_some_any in Heq2.
            exists w; split; simpl.
            + split_and!; try apply name_fresh_action; intuition.
            + simpl in *; cut ((p ∙ w ≡ w) ∧ (q ∙ w ≡ w)); [intros [W1 W2] | split; apply perm_notin_domain_id; auto];
              (* slow *)rewrite <-W1 at 1; (* slow *)rewrite <-W2 at 2; rewrite 2!gact_compat, <-2!perm_comm_distr, <-2!gact_compat, Heq1;
              apply perm_inj; apply Heq2; simpl; intuition.
        - intros []; unfold action, prmact, name_abstraction_action, prod_act, equiv, name_abstraction_equiv;
            apply alpha_equiv_some_any; intros ? ?; simpl in *; rewrite 2!gact_id; reflexivity.
        - intros ? ? []; unfold action, prmact, name_abstraction_action, prod_act, equiv, name_abstraction_equiv;
            apply alpha_equiv_some_any; intros ? ?; simpl in *; rewrite <-2!gact_compat; reflexivity.
    Qed.
    
    #[global] Instance name_abstraction_support: Support name_abs := λ '(_, x), support x.

    #[global] Instance name_abstraction_nominal: Nominal name_abs.
    Proof.
        split.
        - exact name_abstraction_perm.
        - intros [a x] b c ? ?; destruct (decide (b = c)), (decide (b = a)), (decide (c = a)); 
            subst; try (congruence || apply perm_action_equal); 
            unfold action, prmact, name_abstraction_action, prod_act, equiv, name_abstraction_equiv, 
                prod_equiv, support, name_abstraction_support in *.
            + new w fresh (⟨a,c⟩ ∙ a) a (⟨a,c⟩ ∙ x) x; exists w; split; simpl; [intuition |]; 
              rewrite swap_perm_left, (fresh_fixpoint a c x), 2!fresh_fixpoint; auto.
            + new w fresh (⟨b,a⟩ ∙ a) a (⟨b,a⟩ ∙ x) x; exists w; split; simpl; [intuition |]; 
              rewrite swap_perm_right, (fresh_fixpoint b a x), 2!fresh_fixpoint; auto.
            + new w fresh (⟨b,c⟩ ∙ a) a (⟨b,c⟩ ∙ x) x; exists w; split; simpl; [intuition |];
              rewrite swap_perm_neither, (fresh_fixpoint b c x); auto. 
    Qed.
End NameAbstractionNominal.