From Nominal Require Import Nominal Fresh.

Section ProdNominal.
    Context `{Nominal X, Nominal Y}.

    (* Equiv already defined by stdpp *)

    #[export] Instance prod_action: PermAction (X * Y) := λ p '(x, y), (p • x, p • y).
    #[export] Instance prod_support: Support (X * Y) := λ '(x, y), support x ∪ support y.

    #[export] Instance prod_perm: PermT (X * Y).
    Proof.
        split.
        - apply prod_relation_equiv; typeclasses eauto.
        - intros p q Heq1 [a b] [c d] Heq2; unfold equiv, prod_equiv, prod_relation;
            unfold equiv, prod_equiv, prod_relation in Heq2; simpl in *; split; destruct Heq2 as [H3 H4];
            rewrite Heq1; apply perm_inj; assumption.
        - intros [? ?]; unfold action, prod_action, equiv, prod_equiv, prod_relation; simpl; split;
            apply gact_id.
        - intros p q [? ?]; unfold action, prod_action, equiv, prod_equiv, prod_relation; simpl; split;
            apply gact_compat.
    Qed.

    #[export] Instance prod_nominal: Nominal (X * Y).
    Proof.
        split.
        - exact prod_perm.
        - intros [] ? ? ? ?; unfold action, prod_action, equiv, prod_equiv, prod_relation, 
            support, prod_support in *;
            simpl; split; apply support_spec; set_solver.
    Qed. 
End ProdNominal.

(* Freshness properties for prod *)
From Nominal Require Import Instances.Name.

Lemma fresh_prod_iff `{Nominal X, Nominal Y} (a: name) (x: X) (y: Y): a # (x, y) ↔ a # x ∧ a # y.
Proof.
  split; [intros [w [? Hf]] | intros []].
    - unfold support,prod_support,action,prod_action,equiv,prod_equiv,prod_relation in *; simpl in *.
      destruct Hf as [Hf1 Hf2]; split; exists w; split; set_solver.
    - destruct (exist_fresh (support a ∪ support x ∪ support y ∪ support (x, y))) as [w ?]; exists w; split.
      + set_solver.
      + unfold action,equiv,prod_action,prod_equiv,prod_relation; split; simpl; apply fresh_fixpoint; auto;
        fresh_tac.
Qed.