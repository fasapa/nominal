From Coq Require Import Classes.RelationClasses.
From Nominal Require Import Alpha Instances.Name Instances.Prod.

Polymorphic Record NameAbstraction `{Nominal X} := mkAbstraction { abs :> (name * X) }.
Arguments NameAbstraction _ {_ _ _ _}.
Arguments mkAbstraction {_ _ _ _ _} _.
Notation " '[𝔸]' X " := (NameAbstraction X) (at level 1, no associativity, format "[𝔸] X").
Notation " [ a ] x " := ({| abs := (a,x) |}) (at level 1, no associativity, format "[ a ] x").

Instance name_abstraction_equiv `{Nominal X}: Equiv [𝔸]X := (≈α).

Instance name_abstraction_equivalence `{Nominal}: Equivalence name_abstraction_equiv.
Proof.
    pose proof alpha_equivalence_e as EQUIV; split; unfold name_abstraction_equiv; repeat intro;
    [apply EQUIV | apply EQUIV | destruct EQUIV; etransitivity]; eauto.
Qed.

Instance name_abstraction_action `{Nominal X}: PermAction [𝔸]X := λ p a, mkAbstraction (p ∙ (fst a), p ∙ (snd a)). 

Instance name_abstraction_perm `{Nominal X}: Perm [𝔸]X.
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

Instance name_abstraction_support `{Nominal X}: Support [𝔸]X := λ a, support (snd a).

Instance name_abstraction_nominal `{Nominal X}: Nominal [𝔸]X.
Proof. split.
    - exact name_abstraction_perm.
    - intros [[a x]] b c ? ?; destruct (decide (b = c)), (decide (b = a)), (decide (c = a)); 
        subst; try (congruence || apply perm_action_equal); unfold support, name_abstraction_support in *; simpl in *.
        + new w fresh (⟨a,c⟩ ∙ a) a (⟨a,c⟩ ∙ x) x; exists w; split; simpl in *; [intuition |];
          rewrite swap_perm_left, (fresh_fixpoint a c x), 2!fresh_fixpoint; auto.
        + new w fresh (⟨b,a⟩ ∙ a) a (⟨b,a⟩ ∙ x) x; exists w; split; simpl; [intuition |]; 
          rewrite swap_perm_right, (fresh_fixpoint b a x), 2!fresh_fixpoint; auto.
        + new w fresh (⟨b,c⟩ ∙ a) a (⟨b,c⟩ ∙ x) x; exists w; split; simpl; [intuition |];
          rewrite swap_perm_neither, (fresh_fixpoint b c x); auto.
Qed.

(* Basic properties *)
Lemma abs_action `{Nominal X} p a x: p ∙ [a]x = [p ∙ a](p ∙ x).
Proof. auto. Qed.

Lemma abs_support `{Nominal X} a x: support [a]x = support x.
Proof. auto. Qed.