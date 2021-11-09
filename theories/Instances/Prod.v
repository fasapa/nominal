From Nominal Require Import Nominal.

Section ProdNominal.
    Context `{Nominal X, Nominal Y}.

    #[global] Instance prod_act: PermAct (X * Y) :=
        λ p '(x, y), (p ∙ x, p ∙ y).
    
    #[global] Instance prod_perm: Perm (X * Y).
    Proof.
        split.
        - apply prod_relation_equiv; typeclasses eauto.
        - intros p q Heq1 [a b] [c d] Heq2; unfold equiv, prod_equiv, prod_relation;
            unfold equiv, prod_equiv, prod_relation in Heq2; simpl in *; split; destruct Heq2 as [H3 H4];
            rewrite Heq1; apply perm_inj; assumption.
        - intros [? ?]; unfold action, prmact, prod_act, equiv, prod_equiv, prod_relation; simpl; split;
            apply gact_id.
        - intros p q [? ?]; unfold action, prmact, prod_act, equiv, prod_equiv, prod_relation; simpl; split;
            apply gact_compat.
    Qed.
    
    #[global] Instance prod_support: Support (X * Y) :=
        λ '(x, y), support x ∪ support y.

    #[global] Instance prod_nominal: Nominal (X * Y).
    Proof.
        split.
        - exact prod_perm.
        - intros [] ? ? ? ?; unfold action, prmact, prod_act, equiv, prod_equiv, prod_relation, support, prod_support in *;
            simpl; split; apply support_spec; set_solver.
    Qed. 

End ProdNominal.
