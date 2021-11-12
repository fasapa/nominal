From Coq Require Import Classes.RelationClasses.
From Nominal Require Import Alpha Instances.Name Instances.Prod.

Polymorphic Record NameAbstraction `{Nominal X} := mkAbstraction { abs :> (name * X) }.
Arguments NameAbstraction _ {_ _ _ _}.
Arguments mkAbstraction {_ _ _ _ _} _.
Notation " '[𝔸]' X " := (NameAbstraction X) (at level 1, no associativity, format "[𝔸] X").
Notation " [ a ] x " := ({| abs := (a,x) |}) (at level 1, no associativity, format "[ a ] x").

#[export] Instance name_abstraction_equiv `{Nominal X}: Equiv [𝔸]X := (≈α).

#[export] Instance name_abstraction_equivalence `{Nominal}: Equivalence name_abstraction_equiv.
Proof.
    pose proof alpha_equivalence_e as EQUIV; split; unfold name_abstraction_equiv; repeat intro;
    [apply EQUIV | apply EQUIV | destruct EQUIV; etransitivity]; eauto.
Qed.

#[export] Instance name_abstraction_action `{Nominal X}: PermAction [𝔸]X := λ p a, mkAbstraction (p ∙ (fst a), p ∙ (snd a)). 

#[export] Instance name_abstraction_perm `{Nominal X}: Perm [𝔸]X.
Proof.
    Opaque alpha_equiv_e.
    split.
    - exact name_abstraction_equivalence.
    - intros p q Heq1 [[a x]] [[b x']] Heq2;
        unfold action, name_abstraction_action, equiv, name_abstraction_equiv;
        unfold equiv, name_abstraction_equiv in Heq2; simpl in *.
        new w fresh p q a b x x' (p ∙ x) (q ∙ x'); exists w; apply alpha_equiv_some_any in Heq2; split.
        + split_and!; try apply name_fresh_action; auto.
        + cut ((p ∙ w ≡ w) ∧ (q ∙ w ≡ w)); [intros [W1 W2] | split; apply perm_notin_domain_id; auto].
            (* slow *)rewrite <-W1 at 1. (* slow *)rewrite <-W2 at 2.
            rewrite 2!gact_compat, <-2!perm_comm_distr, <-2!gact_compat, Heq1;
            apply perm_inj; apply Heq2; intuition.
    - intros [[]]; unfold action, name_abstraction_action, prod_act, equiv, name_abstraction_equiv; simpl;
        apply alpha_equiv_some_any; intros ? ?; simpl in *; rewrite 2!gact_id; reflexivity.
    - intros ? ? [[]]; unfold action, name_abstraction_action, prod_act, equiv, name_abstraction_equiv;
        apply alpha_equiv_some_any; intros ? ?; simpl in *; rewrite <-2!gact_compat; reflexivity.
Qed.

#[export] Instance name_abstraction_support `{Nominal X}: Support [𝔸]X := λ a, support (abs a).

#[export] Instance name_abstraction_nominal `{Nominal X}: Nominal [𝔸]X.
Proof. split.
    - exact name_abstraction_perm.
    - intros [[a x]] b c ? ?; destruct (decide (b = c)), (decide (b = a)), (decide (c = a)); 
        subst; try (congruence || apply perm_action_equal); unfold support, name_abstraction_support in *; simpl in *.
        + apply support_fresh,fresh_pair_iff in H1 as []; congruence.
        + apply support_fresh,fresh_pair_iff in H2 as []; congruence.
        + new w fresh (⟨b,c⟩ ∙ a) a (⟨b,c⟩ ∙ x) x; exists w; split; simpl; [intuition |];
          rewrite swap_perm_neither, (fresh_fixpoint b c x); auto; apply fresh_pair_iff in H1,H2; intuition.
Qed.

(* Basic properties *)
Lemma nabs_action `{Nominal X} p a x: p ∙ [a]x = [p ∙ a](p ∙ x).
Proof. auto. Qed.

Lemma nabs_support `{Nominal X} a x: support [a]x = support a ∪ support x.
Proof. auto. Qed.

Lemma nabs_inv `{Nominal X} a x x': [a]x ≡ [a]x' ↔ x ≡ x'.
Proof. split; intros HH.
    - unfold equiv, name_abstraction_equiv in HH; apply alpha_inv_name_equiv_iff in HH; auto. 
    - apply (alpha_inv_name_equiv_iff a) in HH; assumption.
Qed.

Lemma lol `{Nominal} a a' x: a' # [a]x ↔ a = a' ∨ a' # x.  
Proof.
    split; intros.
    - destruct (decide (a = a')); subst.
        + left. auto.
        + right; destruct (exist_fresh (support a ∪ support a' ∪ support x ∪ support [a]x)) as [w ?].
            exists w; split; [set_solver |]; apply some_any_iff in H1; cut (w ∉ support [a]x); [intros I | set_solver];
            specialize (H1 w I); unfold equiv,name_abstraction_equiv in H1; simpl in H1.
            assert (L: ⟨ a', w ⟩ ∙ a = a). { rewrite swap_perm_neither; auto; apply not_eq_sym,name_neq_fresh_iff; destruct_notin_union; support_fresh_tac; auto. }
            rewrite L in H1; apply alpha_inv_name_equiv_iff in H1; assumption.
    - assert (L: a = a' → a' # [a]x). {
        intros; subst; destruct (exist_fresh (support a' ∪ support x)) as [w ?]; exists w; split.
        * auto.
        * unfold equiv, name_abstraction_equiv; simpl; rewrite swap_perm_left; apply alpha_inv; right; split.
            -- apply fresh_pair_iff; split; destruct_notin_union; support_fresh_tac; [apply name_neq_fresh_iff |]; auto.
            -- rewrite perm_swap; auto.
    } destruct H1.
        + auto. 
        + destruct (decide (a = a')); subst.
            * auto. 
            * clear L; destruct (exist_fresh (support a ∪ support a' ∪ support x)) as [w ?]; exists w; split.   
                -- unfold support, name_abstraction_support, support, prod_support; simpl; set_solver. 
                -- unfold equiv, name_abstraction_equiv; simpl; rewrite swap_perm_neither; auto.
                    ++ apply alpha_inv_name_equiv_iff; auto; apply fresh_fixpoint; auto; destruct_notin_union; support_fresh_tac; auto.
                    ++ apply not_eq_sym, name_fresh_neq; destruct_notin_union; support_fresh_tac; auto.
Qed.
    