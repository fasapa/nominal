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
Lemma nabs_action `{Nominal X} p a (x: X): p ∙ [a]x = [p ∙ a](p ∙ x).
Proof. auto. Qed.

Lemma nabs_support `{Nominal X} a (x: X): support [a]x = support a ∪ support x.
Proof. auto. Qed.

Lemma nabs_inv `{Nominal X} a (x x': X): [a]x ≡ [a]x' ↔ x ≡ x'.
Proof. split; intros HH.
    - unfold equiv, name_abstraction_equiv in HH; apply alpha_inv_name_equiv_iff in HH; auto. 
    - apply (alpha_inv_name_equiv_iff a) in HH; assumption.
Qed.

Lemma fresh_same_alpha_class `{Nominal X} a (x: X): a # [a]x.
Proof.
    destruct (exist_fresh (support a ∪ support x)) as [w ?]; exists w.
    split; [auto |].
    unfold equiv, name_abstraction_equiv; simpl.
    rewrite swap_perm_left; apply alpha_inv; right; split.
    - apply fresh_pair_iff; split; [| apply support_fresh]; set_solver.
    - rewrite perm_swap; reflexivity.
Qed.

Lemma alpha_class_inv1 `{Nominal X} (a a': name) (x: X): a = a' ∨ a' # x → a' # [a]x.
Proof.
    intros [EqA | F]; [rewrite EqA | destruct (decide (a = a')); subst]; try apply fresh_same_alpha_class.
    destruct (exist_fresh (support a ∪ support a' ∪ support x)) as [w ?]; exists w.
    split; [set_solver |].
    unfold equiv, name_abstraction_equiv; simpl.
    rewrite swap_perm_neither; try set_solver.
    apply alpha_inv_name_equiv_iff, fresh_fixpoint; [assumption | apply support_fresh]; set_solver.
Qed.

Lemma alpha_class_inv2 `{Nominal X} (a a': name) (x: X): a' # [a]x → a = a' ∨ a' # x.
Proof.
    intros F; destruct (decide (a = a')); subst; [intuition |].
    right. (* a ≠ a' *)
    destruct (exist_fresh (support a ∪ support a' ∪ support x ∪ support [a]x)) as [w ?]; exists w.
    split; [set_solver |]; apply some_any_iff in F; cut (w ∉ support [a]x); [intros Hw | set_solver].
    specialize (F w Hw); unfold equiv, name_abstraction_equiv in F. 
    simpl in F. assert (L: ⟨a',w⟩ ∙ a = a). { apply swap_perm_neither; set_solver. }
    rewrite L in F; apply alpha_inv_name_equiv_iff in F; assumption.
Qed.

Lemma alpha_class_inv `{Nominal X} (a a': name) (x: X): a = a' ∨ a' # x ↔ a' # [a]x.
Proof. split; [apply alpha_class_inv1 | apply alpha_class_inv2]. Qed.
    