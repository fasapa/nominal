From Coq Require Import Classes.RelationClasses.
From Nominal Require Import Alpha.
From Nominal.Instances Require Import Name Prod Perm.

#[universes(template=no)]
Record NameAbstraction `{Nominal X} := mkAbstraction { abs :> (Name * X) }.
Arguments NameAbstraction _ {_ _ _ _}.
Arguments mkAbstraction {_ _ _ _ _} _.
Notation " '[𝔸]' X " := (NameAbstraction X) (at level 1, no associativity, format "[𝔸] X").
Notation " [ a ] x " := ({| abs := (a,x) |}) (at level 1, no associativity, format "[ a ] x").

#[export] Instance name_abstraction_action `{Nominal X}: PermAction [𝔸]X := 
    λ p a, mkAbstraction (p • (fst a), p • (snd a)). 

#[export] Instance name_abstraction_support `{Nominal X}: Support [𝔸]X := 
    fun ax => let (a,x) := abs ax in (support x) ∖ {[a]}.
    
(* Given X nominal, the pair (name * X) is a nominal type module (≈α) *)
#[export] Instance name_abstraction_equiv `{Nominal X}: Equiv [𝔸]X := (≈α).
#[export] Instance name_abstraction_equivalence `{Nominal X}: Equivalence (name_abstraction_equiv (X := X)).
Proof.
    split; unfold name_abstraction_equiv; repeat intro.
    - destruct x as [[a x]]; simpl; new b fresh a x; fresh_tac; exists b; split; intuition.
    - destruct x as [[a x]]; destruct y as [[b y]]; simpl in *; destruct H1 as [c []];
        exists c; split; intuition.
    - destruct x as [[a x]]; destruct y as [[b y]]; destruct z as [[c z]]; apply alpha_some_any in H1,H2;
        simpl in *; new f fresh a b c x y z; fresh_tac; exists f; split; [intuition | etransitivity]; 
        [eapply H1 | eapply H2]; intuition.
Qed.

#[export] Instance name_abstraction_perm `{Nominal X}: PermT [𝔸]X.
Proof.
    Opaque alpha_equiv_e.
    split.
    - exact name_abstraction_equivalence.
    - intros p q Heq1 [[a x]] [[b y]] Heq2.
        unfold action, name_abstraction_action, equiv, name_abstraction_equiv.
        unfold equiv, name_abstraction_equiv in Heq2; simpl in *.
        new w fresh p q a b x y (p • x) (q • y); exists w; apply alpha_some_any in Heq2; split.
        + split_and!; try apply name_fresh_action; split_union; apply support_fresh; auto.
        + cut ((p • w ≡ w) ∧ (q • w ≡ w)); [intros [W1 W2] | split; apply perm_notin_domain_id; auto].
            (* slow *)rewrite <-W1 at 1; (* slow *)rewrite <-W2 at 2.
            rewrite 2!gact_compat, <-2!perm_comm_distr, <-2!gact_compat, Heq1.
            apply perm_inj. unfold alpha_equiv_a in *; apply Heq2; split_and!; split_union;
            apply support_fresh; auto. split_union. split_union.
    - intros [[a x]]; unfold action, name_abstraction_action, prod_action, equiv, name_abstraction_equiv; simpl.
        apply alpha_some_any; intros w ?; rewrite 2!gact_id; reflexivity.
    - intros ? ? [[a x]]; unfold action, name_abstraction_action, prod_action, equiv, name_abstraction_equiv;
        apply alpha_some_any; intros w ?; simpl in *; rewrite <-2!gact_compat; reflexivity.
Qed.

#[export] Instance name_abstraction_nominal `{Nominal X}: Nominal [𝔸]X.
Proof. split.
    - exact name_abstraction_perm.
    - intros [[a x]] b c ? ?; destruct (decide (b = c)), (decide (b = a)), (decide (c = a));
          try (subst; congruence || subst; apply perm_action_equal); unfold support, name_abstraction_support in *; simpl in *.
        + subst; apply not_elem_of_difference in H1 as []; apply not_elem_of_difference in H2 as [].   (* subst. apply support_fresh in H1. as [?%name_neq_fresh_iff ?]. congruence. *)
          * unfold action,equiv,name_abstraction_equiv,name_abstraction_action ; simpl.
            rewrite name_action_left. pose proof (@Equivalence_Symmetric _ _ alpha_equivalence_e) as S.
            symmetry; apply alpha_rename, support_fresh; auto.
          * set_solver.
          * unfold action,equiv,name_abstraction_equiv,name_abstraction_action ; simpl.
            rewrite name_action_left. pose proof (@Equivalence_Symmetric _ _ alpha_equivalence_e) as S.
            symmetry; apply alpha_rename, support_fresh; auto.
          * set_solver.  
        + subst; apply not_elem_of_difference in H1 as []; apply not_elem_of_difference in H2 as [].
          * unfold action,equiv,name_abstraction_equiv,name_abstraction_action ; simpl.
            rewrite name_action_right; pose proof (@Equivalence_Symmetric _ _ alpha_equivalence_e) as S.
            symmetry. apply alpha_rename_swap, support_fresh; auto.
          * unfold action,equiv,name_abstraction_equiv,name_abstraction_action ; simpl.
            rewrite name_action_right; pose proof (@Equivalence_Symmetric _ _ alpha_equivalence_e) as S.
            symmetry; apply alpha_rename_swap, support_fresh; auto.
          * set_solver.
          * set_solver. 
        + new z fresh (⟨b,c⟩ • a) a (⟨b,c⟩ • x) x; fresh_tac; exists z; simpl; split; simpl; [intuition |].
          rewrite perm_swap_neither, (fresh_fixpoint b c x); auto.
          * apply not_elem_of_difference in H1 as []; apply support_fresh; auto; set_solver.
          * apply not_elem_of_difference in H2 as []; apply support_fresh; auto; set_solver.
Qed.

(* Basic properties *)
Lemma name_abstraction_rename `{Nominal X} (a b: Name) (x: X): 
    b#x → [a]x ≡ [b](⟨a,b⟩ • x).
Proof. apply alpha_rename. Qed.

Lemma name_abstraction_rename_swap `{Nominal X} (a b: Name) (x: X): 
    b#x → [a]x ≡ [b](⟨b,a⟩ • x).
Proof. apply alpha_rename_swap. Qed.

Lemma nabs_action `{Nominal X} p a (x: X): p • [a]x = [p • a](p • x).
Proof. auto. Qed.

Lemma nabs_support `{Nominal X} a (x: X): support [a]x = support x ∖ {[a]}.
Proof. auto. Qed.

Lemma nabs_inv `{Nominal X} a (x x': X): [a]x ≡ [a]x' ↔ x ≡ x'.
Proof. split; intros HH.
    - unfold equiv, name_abstraction_equiv in HH; apply alpha_inv_name_equiv_iff in HH; auto. 
    - apply (alpha_inv_name_equiv_iff a) in HH; assumption.
Qed.

Lemma fresh_same_alpha_class `{Nominal X} a (x: X): a # [a]x.
Proof.
    destruct (exist_fresh (support x ∖ {[a]})) as [w ?]; exists w.
    split; [auto |].
    apply not_elem_of_difference in H1 as [].
    + unfold equiv, name_abstraction_equiv; simpl.
      rewrite name_action_left; pose proof (@Equivalence_Symmetric _ _ alpha_equivalence_e) as S;
      symmetry; apply alpha_rename, support_fresh; assumption.
    + apply elem_of_singleton in H1; subst; apply perm_action_equal.
Qed.

Lemma alpha_class_inv1 `{Nominal X} (a a': Name) (x: X): 
    a = a' ∨ (a ≠ a' ∧ a' # x) → a' # [a]x.
Proof.
    intros [EqA | [? F]]; [rewrite EqA | destruct (decide (a = a')); subst]; try apply fresh_same_alpha_class.
    destruct (exist_fresh (support a ∪ support a' ∪ support x)) as [w ?]; exists w.
    split; [set_solver |].
    unfold equiv, name_abstraction_equiv; simpl.
    rewrite perm_swap_neither; try set_solver.
    apply alpha_inv_name_equiv_iff, fresh_fixpoint; [assumption | apply support_fresh]; set_solver.
Qed.

Lemma alpha_class_inv2 `{Nominal X} (a a': Name) (x: X): 
    a' # [a]x → a = a' ∨ (a ≠ a' ∧ a' # x).
Proof.
    intros F; destruct (decide (a = a')); subst; [intuition |].
    right. (* a ≠ a' *) split; auto.
    destruct (exist_fresh (support a ∪ support a' ∪ support x ∪ support [a]x)) as [w ?]; exists w.
    split; [set_solver |]; apply some_any_iff in F; cut (w ∉ support [a]x); [intros Hw | set_solver].
    specialize (F w Hw); unfold equiv, name_abstraction_equiv in F. 
    simpl in F. assert (L: ⟨a',w⟩ • a = a). { apply perm_swap_neither; set_solver. }
    rewrite L in F; apply alpha_inv_name_equiv_iff in F; assumption.
Qed.

Lemma alpha_class_inv `{Nominal X} (a a': Name) (x: X): 
    a = a' ∨ (a ≠ a' ∧ a' # x) ↔ a' # [a]x.
Proof. split; [apply alpha_class_inv1 | apply alpha_class_inv2]. Qed.

#[global] Instance name_abstraction_rw1 `{Nominal X}: 
    ∀a, Proper (equiv ==> alpha_equiv_e) (pair a).
Proof. repeat intro; apply alpha_inv_iff; left; tauto. Qed.

#[global] Instance name_abstraction_rw2 `{Nominal X}: 
    Proper (alpha_equiv_e ==> (@name_abstraction_equiv X _ _ _ _)) mkAbstraction.
Proof. repeat intro; unfold name_abstraction_equiv; simpl; assumption. Qed.

#[global] Instance name_abstraction_rw3 `{Nominal X}: 
    Proper ((@name_abstraction_equiv X _ _ _ _) ==> (@name_abstraction_equiv X _ _ _ _) ==> flip impl) equiv.
Proof.
    repeat intro; unfold name_abstraction_equiv in *; 
    destruct x as [[a x]]; destruct y as [[a' x']];
    destruct x0 as [[b z]]; destruct y0 as [[b' z']]; simpl; unfold equiv in *.
    (* for some reason Coq cant find an instance for Transitive or Symmetric alpha_equiv_e *)
    pose proof (@Equivalence_Transitive _ _ alpha_equivalence_e) as T.
    pose proof (@Equivalence_Symmetric _ _ alpha_equivalence_e) as S.
    apply T with [a']x'; auto; apply T with [b']z'; auto.
Qed.

#[global] Instance name_abstraction_rw4 `{Nominal X}: 
    ∀ a (x : X), ProperProxy ((@name_abstraction_equiv X _ _ _ _)) [a]x.
Proof. 
    unfold ProperProxy,name_abstraction_equiv; repeat intro.
    pose proof (@Equivalence_Reflexive _ _ alpha_equivalence_e) as F.
    auto.
Qed.

Lemma name_abstraction_inv `{Nominal} (a b: Name) (x y: X):
    [a]x ≡ [b]y ↔ (a = b ∧ x ≡ y) ∨ ((a # [b]y) ∧ x ≡ ⟨a,b⟩ • y).
Proof.
    split; intro HH.
    - apply alpha_inv_iff in HH as [? | [HHH ?]].
        + left; assumption.
        + right; split; try tauto; apply alpha_class_inv; right; apply fresh_prod_iff in HHH as []; split.
            * apply not_eq_sym, name_neq_fresh_iff; assumption.
            * assumption. 
    - destruct HH as [[] | [HH1 HH2]].
        + subst; rewrite H2; reflexivity.
        + apply alpha_class_inv in HH1 as []; subst.
            * apply nabs_inv; rewrite HH2; apply perm_action_equal.
            * apply alpha_inv_iff; right; split.
                -- apply fresh_prod_iff; split; [apply name_fresh_iff,name_neq_fresh_iff |]; tauto.
                -- assumption.
Qed.

(* Concretion *)
Section Concretion.
    Context `{Nominal X}.

    Definition concretion (F: [𝔸]X) (b: Name): option X :=
       let (a,x) := abs F in
       if (decide (a = b)) then Some x else
       if (decide (b ∉ support x)) then Some (⟨a,b⟩ • x)
       else None.
    
    Lemma concretion_eq a b (x: X): 
        a = b → concretion ([a]x) b ≡ Some x.
    Proof. 
        intros; subst; unfold concretion; simpl; destruct (decide _); subst;
        [reflexivity | congruence].
    Qed.

    Lemma concretion_notin a b (x: X): 
        a ≠ b → b ∉ support x → concretion ([a]x) b ≡ Some (⟨a,b⟩ • x).
    Proof. 
        intros; subst; unfold concretion; simpl; destruct (decide _); subst;
        [congruence | destruct (decide _); [reflexivity | set_solver]]. 
    Qed.
    
End Concretion.