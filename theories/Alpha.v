From Coq Require Import Classes.RelationClasses.
From Nominal Require Export Nominal Fresh Instances.Name Instances.Prod.

(* Two (equivalent, see below) flavors of alpha relation. 
   The notation "... | 0" means alpha_equiv_e has priority in the proof search *)
#[export] Instance alpha_equiv_e `{Nominal X}: Equiv (Name * X) | 0 := 
    λ '(a,x) '(b,y), ∃ (c: Name), c #[a, b, x, y] ∧ ⟨c,a⟩ • x ≡@{X} ⟨c,b⟩ • y.

#[export] Instance alpha_equiv_a `{Nominal X}: Equiv (Name * X) | 1 := 
    λ '(a,x) '(b,y), ∀ (c: Name), c #[a, b, x, y] → ⟨c,a⟩ • x ≡@{X} ⟨c,b⟩ • y.

Infix "≈α" := (alpha_equiv_e) (at level 70, no associativity).
Infix "≈αₐ" := (alpha_equiv_a) (at level 70, no associativity).
Notation "(≈α)" := (alpha_equiv_e) (only parsing).
Notation "(≈αₐ)" := (alpha_equiv_a) (only parsing).

(* Alpha relation analogue to freshness some/any *)
Lemma alpha_some_any `{Nominal X} (a b: Name) (x y: X): (a, x) ≈α (b, y) ↔ (a, x) ≈αₐ (b, y).
Proof.
    split; intros Ha; unfold alpha_equiv_e, alpha_equiv_a in *.
    - intros; simpl in *; destruct Ha as [w [? Ha]]; destruct_and!;
        rewrite (perm_expand _ w a), (perm_expand _ w b), <-!gact_compat, 
            (fresh_fixpoint _ _ x), (fresh_fixpoint _ _ y), Ha;
        try (apply not_eq_sym, name_neq_fresh_iff); auto.
    - new c fresh a b x y; fresh_tac; exists c; split; [| apply Ha]; fresh_tac; intuition.
Qed.

(* Alpha relation is an equivalence. *)
#[export] Instance alpha_equivalence_e `{Nominal X}: Equivalence (@alpha_equiv_e X _ _ _ _).
Proof.
    split.
    - intros [a x]; destruct (exist_fresh (support a ∪ support x)) as [y []%not_elem_of_union];
        exists y; split_and!; simpl; try (apply support_fresh); auto.
    - intros [? ?] [? ?] [z ?]; exists z; intuition. 
    - intros [a x] [b y] [c z] A A'; simpl in *;
        new f fresh a x b y c z; fresh_tac; apply alpha_some_any in A,A'; exists f; split; simpl;
            [| rewrite (A f), (A' f)]; intuition. 
Qed.

#[export] Instance alpha_equivalence_a `{Nominal X}: Equivalence (@alpha_equiv_a X _ _ _ _).
Proof.
    split.
    - intros [] ? ?; simpl; reflexivity.
    - intros [] [] HH b ?; specialize (HH b); intuition.
    - intros [] [q p] [] H1 H2; apply alpha_some_any in H1,H2; apply alpha_some_any.
        (* for some reason Coq cant find an instance for Transitive alpha_equiv_e, even though its
           define just above. *)
        pose proof (@Equivalence_Transitive _ _ alpha_equivalence_e).
        transitivity (q, p); auto.
Qed.

Lemma alpha_rename `{Nominal X} (a b: Name) (x: X): b#x → (a,x) ≈α (b, ⟨a,b⟩ • x).
Proof.
    intros; destruct (decide (a = b)); subst.
    - apply alpha_some_any; repeat intro; simpl in *; rewrite perm_action_equal; reflexivity.
    - new c fresh a b x (⟨a,b⟩ • x); fresh_tac; exists c; simpl; split; [intuition |]; 
        rewrite (perm_expand _ b _), <-2!gact_compat, (fresh_fixpoint c b x), (swap_perm b a); auto.
        apply not_eq_sym,name_neq_fresh_iff; auto.
Qed.

Lemma alpha_rename_swap `{Nominal X} (a b: Name) (x: X): b#x → (a,x) ≈α (b, ⟨b,a⟩ • x).
Proof.
    intros; destruct (decide (a = b)); subst.
    - apply alpha_some_any; repeat intro; simpl in *; rewrite perm_action_equal; reflexivity.
    - new c fresh a b x (⟨b,a⟩ • x); fresh_tac; exists c; simpl; split; [intuition |]; 
        rewrite (perm_expand _ b _), <-2!gact_compat, (fresh_fixpoint c b x), (swap_perm b a); auto.
        apply not_eq_sym,name_neq_fresh_iff; auto.
Qed.

(* Alpha relation properties *)
Lemma alpha_inv1 `{Nominal X} (a b: Name) (x y: X): 
    (a,x) ≈α (b,y) → ((a = b ∧ x ≡ y) ∨ (a #(b,y) ∧ x ≡ ⟨a,b⟩ • y)).
Proof.
    destruct (decide (a = b)); subst; intros [w [wFr wFx]].
    - left; split; [reflexivity |]; eapply perm_inj; intuition; eassumption.
    - right; cut (a # b ∧ a # y); [intros [] |].
        + split; [apply fresh_prod_iff; intuition |].
            rewrite (perm_expand _ w _), <-!gact_compat, (fresh_fixpoint a w y), <-wFx, swap_perm; intuition; subst.
            * symmetry; apply perm_action_duplicate.
            * eapply name_fresh_false; eauto. 
        + split; [apply name_neq_fresh_iff; assumption |].
          cut (⟨w,b⟩ • ⟨w,b⟩ • y ≡ y); [intros HH1 | apply perm_action_duplicate].
          cut (⟨w,b⟩ • ⟨w,a⟩ • w = a); [intros HH2 | rewrite perm_swap_left, perm_swap_neither; auto; apply not_eq_sym, name_neq_fresh_iff; intuition].
          rewrite <-HH1,<-wFx; rewrite <-HH2 at 1; do 2 apply fresh_equivariant; intuition.
Qed.

Lemma alpha_inv2 `{Nominal X} (a b: Name) (x y: X): 
    ((a = b ∧ x ≡ y) ∨ (a # (b,y) ∧ x ≡ ⟨a,b⟩ • y)) → (a,x) ≈α (b,y).
Proof.
    intros [[? HH] | [HH1%fresh_prod_iff HH2]]; new w fresh a b x y; fresh_tac; subst; exists w.
    - split; [intuition |]; rewrite HH; reflexivity.
    - split; [intuition |]; rewrite HH2, (perm_expand w a b), <-!gact_compat, (fresh_fixpoint w a y);
        intuition; subst; eapply name_fresh_false; eauto.
Qed.

Lemma alpha_inv_iff `{Nominal X} (a b: Name) (x y: X): 
    (a,x) ≈α (b,y) ↔ (a = b ∧ x ≡ y) ∨ (a # (b,y) ∧ x ≡ ⟨a,b⟩ • y).
Proof. split; [apply alpha_inv1 | apply alpha_inv2]. Qed.

Corollary alpha_inv_name_equiv_iff `{Nominal X} (a: Name) (x y: X): 
    (a, x) ≈α (a, y) ↔ x ≡ y.
Proof.
    split; intros HH.
    - apply alpha_inv_iff in HH as [? | [? H1]]; [| rewrite perm_action_equal in H1]; intuition.
    - apply alpha_inv_iff; left; intuition.
Qed.

Lemma alpha_equivar `{Nominal X} (p: Perm) (a b: Name) (x y: X): 
    (a,x) ≈α (b,y) → (p • a, p • x) ≈α (p • b, p • y).
Proof.
    intro HA; apply alpha_inv_iff; apply alpha_inv_iff in HA as [[? Hxy] | [Hby ?]].
    - left; split; subst; [| rewrite Hxy]; auto.
    - right; split.
        + apply fresh_prod_iff in Hby as []; apply fresh_prod_iff; split; apply fresh_equivariant; auto.
        + rewrite <-perm_swap_distr; apply perm_inj; assumption.
Qed.