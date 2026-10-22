From Coq Require Import Classes.RelationClasses.
From Nominal Require Export Nominal Fresh.
From Nominal.Instances Require Import Name Prod Perm.

#[universes(template=no),projections(primitive=yes)]
Record NameAbstraction `{Nominal X} := mkAbstraction { name: Name; term: X }.
Arguments NameAbstraction _ {_ _ _ _}.
Arguments mkAbstraction {_ _ _ _ _} _.
Notation " '[𝔸]' X " := (NameAbstraction X) (at level 1, no associativity, format "[𝔸] X").
Notation " ⟦ a ⟧ x " := ({| name := a; term := x |}) (at level 1, no associativity, format "⟦ a ⟧ x").

#[export] Instance name_abstraction_action `{Nominal X}: PermAction [𝔸]X := 
    λ p abs, mkAbstraction (p • abs.(name)) (p • abs.(term)). 

#[export] Instance name_abstraction_support `{Nominal X}: Support [𝔸]X := 
    fun abs => (support abs.(term)) ∖ {[abs.(name)]}.

(* Old Alpha.v *)

#[export] Instance alpha_equiv_e `{Nominal X}: Equiv [𝔸]X | 0 :=
    λ x y, ∃ (c: Name), c #[x.(name), y.(name), x.(term), y.(term)] ∧ ⟨c,x.(name)⟩•x.(term) ≡@{X} ⟨c,y.(name)⟩•y.(term).

#[export] Instance alpha_equiv_a `{Nominal X}: Equiv [𝔸]X | 1 := 
    λ x y, ∀ (c: Name), c #[x.(name), y.(name), x.(term), y.(term)] → ⟨c,x.(name)⟩•x.(term) ≡@{X} ⟨c,y.(name)⟩•y.(term).

Infix "≈α" := (alpha_equiv_e) (at level 70, no associativity).
Infix "≈αₐ" := (alpha_equiv_a) (at level 70, no associativity).
Notation "(≈α)" := (alpha_equiv_e) (only parsing).
Notation "(≈αₐ)" := (alpha_equiv_a) (only parsing).

(* Alpha relation analogue to freshness some/any *)
Lemma alpha_some_any `{Nominal X} (a b: Name) (x y: X): ⟦a⟧x ≈α ⟦b⟧y ↔ ⟦a⟧x ≈αₐ ⟦b⟧y.
Proof.
    split; intros Ha. unfold alpha_equiv_e, alpha_equiv_a in *; simpl in *.
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
        transitivity ⟦q⟧p; auto.
Qed.

Lemma alpha_rename `{Nominal X} (a b: Name) (x: X): b#x → ⟦a⟧x ≈α ⟦b⟧(⟨a,b⟩•x).
Proof.
    intros; destruct (decide (a = b)); subst.
    - apply alpha_some_any; repeat intro; simpl in *; rewrite perm_action_equal; reflexivity.
    - new c fresh a b x (⟨a,b⟩ • x); fresh_tac; exists c; simpl; split; [intuition |]; 
        rewrite (perm_expand _ b _), <-2!gact_compat, (fresh_fixpoint c b x), (swap_perm b a); auto.
        apply not_eq_sym,name_neq_fresh_iff; auto.
Qed.

Lemma alpha_rename_swap `{Nominal X} (a b: Name) (x: X): b#x → ⟦a⟧x ≈α ⟦b⟧(⟨b,a⟩•x).
Proof.
    intros; destruct (decide (a = b)); subst.
    - apply alpha_some_any; repeat intro; simpl in *; rewrite perm_action_equal; reflexivity.
    - new c fresh a b x (⟨b,a⟩ • x); fresh_tac; exists c; simpl; split; [intuition |]; 
        rewrite (perm_expand _ b _), <-2!gact_compat, (fresh_fixpoint c b x), (swap_perm b a); auto.
        apply not_eq_sym,name_neq_fresh_iff; auto.
Qed.

(* Alpha relation properties *)
Lemma alpha_inv_left `{Nominal X} (a b: Name) (x y: X): 
    ⟦a⟧x ≈α ⟦b⟧y → ((a = b ∧ x ≡ y) ∨ (a #(b,y) ∧ x ≡ ⟨a,b⟩•y)).
Proof.
    destruct (decide (a = b)); subst; intros [w [wFr wFx]].
    - left; split; [reflexivity |]; eapply perm_inj; intuition; eassumption.
    - right; cut (a # b ∧ a # y); [intros [] |].
        + split; [apply fresh_prod_iff; intuition |].
            rewrite (perm_expand _ w _), <-!gact_compat, (fresh_fixpoint a w y), <-wFx, swap_perm; intuition; subst.
            * symmetry; apply perm_action_duplicate.
            * eapply name_fresh_false; eauto. 
        + simpl in *; split; [apply name_neq_fresh_iff; assumption |].
          cut (⟨w,b⟩ • ⟨w,b⟩ • y ≡ y); [intros HH1 | apply perm_action_duplicate].
          cut (⟨w,b⟩ • ⟨w,a⟩ • w = a); [intros HH2 | rewrite perm_swap_left, perm_swap_neither; auto; apply not_eq_sym, name_neq_fresh_iff; intuition].
          rewrite <-HH1,<-wFx; rewrite <-HH2 at 1; do 2 apply fresh_equivariant; intuition.
Qed.

Lemma alpha_inv_right `{Nominal X} (a b: Name) (x y: X): 
    ((a = b ∧ x ≡ y) ∨ (a # (b,y) ∧ x ≡ ⟨a,b⟩•y)) → ⟦a⟧x ≈α ⟦b⟧y.
Proof.
    intros [[? HH] | [HH1%fresh_prod_iff HH2]]; new w fresh a b x y; fresh_tac; subst; exists w; simpl in *.
    - split; [intuition |]; rewrite HH; reflexivity.
    - split; [intuition |]; rewrite HH2, (perm_expand w a b), <-!gact_compat, (fresh_fixpoint w a y);
        intuition; subst; eapply name_fresh_false; eauto.
Qed.

Lemma alpha_inv_iff `{Nominal X} (a b: Name) (x y: X): 
    ⟦a⟧x ≈α ⟦b⟧y ↔ (a = b ∧ x ≡ y) ∨ (a # (b,y) ∧ x ≡ ⟨a,b⟩•y).
Proof. split; [apply alpha_inv_left | apply alpha_inv_right]. Qed.

Corollary alpha_inv_name_equiv_iff `{Nominal X} (a: Name) (x y: X): 
    ⟦a⟧x ≈α ⟦a⟧y ↔ x ≡ y.
Proof.
    split; intros HH.
    - apply alpha_inv_iff in HH as [? | [? H1]]; [| rewrite perm_action_equal in H1]; intuition.
    - apply alpha_inv_iff; left; intuition.
Qed.

Lemma alpha_equivar `{Nominal X} (p: Perm) (a b: Name) (x y: X): 
    ⟦a⟧x ≈α ⟦b⟧y → ⟦p•a⟧(p•x) ≈α ⟦p•b⟧(p•y).
Proof.
    intro HA; apply alpha_inv_iff; apply alpha_inv_iff in HA as [[? Hxy] | [Hby ?]].
    - left; split; subst; [| rewrite Hxy]; auto.
    - right; split.
        + apply fresh_prod_iff in Hby as []; apply fresh_prod_iff; split; apply fresh_equivariant; auto.
        + rewrite <-perm_swap_distr; apply perm_inj; assumption.
Qed.

(* Old Alpha.v *)

(* Given X nominal, the pair (name * X) is a nominal type module (≈α) *)
#[export] Instance name_abstraction_equiv `{Nominal X}: Equiv [𝔸]X := (≈α).
#[export] Instance name_abstraction_equivalence `{Nominal X}: Equivalence name_abstraction_equiv.
Proof.
    split; unfold name_abstraction_equiv; repeat intro.
    - new b fresh x.(name) x.(term); fresh_tac; exists b; split; auto.
    - destruct H1 as [c []]; exists c; split; intuition.
    - apply alpha_some_any in H1,H2. new f fresh x.(name) y.(name) z.(name) x.(term) y.(term) z.(term); fresh_tac;
      exists f; split; [intuition | etransitivity]; [eapply H1 | eapply H2]; intuition.
Qed.

#[export] Instance name_abstraction_perm `{Nominal X}: PermT [𝔸]X.
Proof.
    Opaque alpha_equiv_e.
    split.
    - exact name_abstraction_equivalence.
    - intros p q Heq1 x y Heq2.
        unfold action, name_abstraction_action, equiv, name_abstraction_equiv.
        unfold equiv, name_abstraction_equiv in Heq2; simpl in *.
        new w fresh p q x.(name) y.(name) x.(term) y.(term) (p•x.(term)) (q•y.(term));
        exists w; apply alpha_some_any in Heq2; split.
        + split_and!; try apply name_fresh_action; split_union; apply support_fresh; auto.
        + cut ((p • w ≡ w) ∧ (q • w ≡ w)); [intros [W1 W2] | split; apply perm_notin_domain_id; auto].
            simpl in *; (* slow *)rewrite <-W1 at 1; (* slow *)rewrite <-W2 at 2.
            rewrite 2!gact_compat, <-2!perm_comm_distr, <-2!gact_compat, Heq1.
            apply perm_inj. unfold alpha_equiv_a in *; apply Heq2; split_and!; split_union;
            apply support_fresh; auto. split_union. split_union.
    - intros x; unfold action, name_abstraction_action, equiv, name_abstraction_equiv; simpl.
        apply alpha_some_any; intros w ?; simpl; rewrite 2!gact_id; reflexivity.
    - intros ? ? x; unfold action, name_abstraction_action, prod_action, equiv, name_abstraction_equiv; simpl.
        apply alpha_some_any; intros w ?; simpl in *; rewrite <-2!gact_compat; reflexivity.
Qed.

#[export] Instance name_abstraction_nominal `{Nominal X}: Nominal [𝔸]X.
Proof. split.
    - exact name_abstraction_perm.
    - intros x a b ? ?; destruct (decide (a = b)), (decide (a = x.(name))), (decide (b = x.(name)));
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
        + new z fresh (⟨a,b⟩ • x.(name)) x.(name) (⟨a,b⟩ • x.(term)) x.(term); fresh_tac; exists z; simpl; repeat (split; auto).
          rewrite perm_swap_neither, (fresh_fixpoint a b x.(term)); auto.
          * apply not_elem_of_difference in H1 as []; apply support_fresh; auto; set_solver.
          * apply not_elem_of_difference in H2 as []; apply support_fresh; auto; set_solver.
Qed.

(* Basic properties *)
Lemma name_abstraction_rename `{Nominal X} (a b: Name) (x: X): 
    b#x → ⟦a⟧x ≡ ⟦b⟧(⟨a,b⟩•x).
Proof. apply alpha_rename. Qed.

Lemma name_abstraction_rename_swap `{Nominal X} (a b: Name) (x: X): 
    b#x → ⟦a⟧x ≡ ⟦b⟧(⟨b,a⟩•x).
Proof. apply alpha_rename_swap. Qed.

Lemma nabs_action `{Nominal X} p a (x: X): p•(⟦a⟧x) = ⟦p•a⟧(p•x).
Proof. auto. Qed.

Lemma nabs_support `{Nominal X} a (x: X): support ⟦a⟧x = support x ∖ {[a]}.
Proof. auto. Qed.

Lemma nabs_inv `{Nominal X} a (x x': X): ⟦a⟧x ≡ ⟦a⟧x' ↔ x ≡ x'.
Proof. split; intros HH.
    - unfold equiv, name_abstraction_equiv in HH; apply alpha_inv_name_equiv_iff in HH; auto. 
    - apply (alpha_inv_name_equiv_iff a) in HH; assumption.
Qed.

Lemma fresh_same_nabs `{Nominal X} a (x: X): a # ⟦a⟧x.
Proof.
    destruct (exist_fresh (support x ∖ {[a]})) as [w ?]; exists w.
    split; [auto |].
    apply not_elem_of_difference in H1 as [].
    + unfold equiv, name_abstraction_equiv; simpl.
      rewrite nabs_action, name_action_left; pose proof (@Equivalence_Symmetric _ _ alpha_equivalence_e) as S;
      symmetry; apply alpha_rename, support_fresh; assumption.
    + apply elem_of_singleton in H1; subst; apply perm_action_equal.
Qed.

Lemma fresh_nabs_left `{Nominal X} (a a': Name) (x: X): 
    a = a' ∨ (a ≠ a' ∧ a' # x) → a' # ⟦a⟧x.
Proof.
    intros [EqA | [? F]]; subst; [apply fresh_same_nabs |].
    destruct (exist_fresh (support a ∪ support a' ∪ support x)) as [w ?]; exists w;
    split; [set_solver |].
    unfold equiv, name_abstraction_equiv; simpl.
    rewrite nabs_action,perm_swap_neither; try set_solver.
    apply alpha_inv_name_equiv_iff, fresh_fixpoint;
    [assumption | apply support_fresh]; set_solver.
Qed.

Lemma fresh_nabs_right `{Nominal X} (a a': Name) (x: X): 
    a' # ⟦a⟧x → a = a' ∨ (a ≠ a' ∧ a' # x).
Proof.
    intros F; destruct (decide (a = a')); subst; [intuition |].
    right. (* a ≠ a' *) split; auto.
    destruct (exist_fresh (support a ∪ support a' ∪ support x ∪ support ⟦a⟧x)) as [w ?]; exists w.
    split; [set_solver |]; apply some_any_iff in F; cut (w ∉ support ⟦a⟧x); [intros Hw | set_solver].
    specialize (F w Hw); unfold equiv, name_abstraction_equiv in F; rewrite nabs_action in F. 
    simpl in F. assert (L: ⟨a',w⟩ • a = a). { apply perm_swap_neither; set_solver. }
    rewrite L in F; apply alpha_inv_name_equiv_iff in F; assumption.
Qed.

Lemma fresh_nabs `{Nominal X} (a a': Name) (x: X): 
    a = a' ∨ (a ≠ a' ∧ a' # x) ↔ a' # ⟦a⟧x.
Proof. split; [apply fresh_nabs_left | apply fresh_nabs_right]. Qed.

#[global] Instance name_abstraction_proper `{Nominal X}: 
    Proper (equiv ==> equiv ==> (@name_abstraction_equiv X _ _ _ _)) mkAbstraction.
Proof. repeat intro; unfold name_abstraction_equiv; simpl; rewrite H1; apply alpha_inv_name_equiv_iff; assumption. Qed.


#[global] Instance name_abstraction_rw1 `{Nominal X}: 
    ∀ a, Proper (equiv ==> (@name_abstraction_equiv X _ _ _ _)) (mkAbstraction a).
Proof. repeat intro. unfold name_abstraction_equiv; apply alpha_inv_name_equiv_iff; auto. Qed.

#[global] Instance name_abstraction_rw2 `{Nominal X}: 
    Proper ((@name_abstraction_equiv X _ _ _ _) ==> (@name_abstraction_equiv X _ _ _ _) ==> flip impl) equiv.
Proof.
    repeat intro. unfold name_abstraction_equiv in *.
    pose proof (@Equivalence_Transitive _ _ alpha_equivalence_e) as T.
    pose proof (@Equivalence_Symmetric _ _ alpha_equivalence_e) as S.
    apply T with ⟦y.(name)⟧y.(term); auto; apply T with ⟦y0.(name)⟧y0.(term); auto.
Qed.

#[global] Instance name_abstraction_rw3 `{Nominal X}: 
    ∀ a (x : X), ProperProxy (@name_abstraction_equiv X _ _ _ _) ⟦a⟧x.
Proof. 
    unfold ProperProxy,name_abstraction_equiv; repeat intro.
    pose proof (@Equivalence_Reflexive _ _ alpha_equivalence_e) as F.
    auto.
Qed.

Lemma name_abstraction_inv `{Nominal X} (a b: Name) (x y: X):
    ⟦a⟧x ≡ ⟦b⟧y ↔ (a = b ∧ x ≡ y) ∨ ((a # ⟦b⟧y) ∧ x ≡ ⟨a,b⟩•y).
Proof.
    split; intro HH.
    - apply alpha_inv_iff in HH as [? | [HHH ?]].
        + left; assumption.
        + right; split; try tauto; apply fresh_nabs; right; apply fresh_prod_iff in HHH as []; split.
            * apply not_eq_sym, name_neq_fresh_iff; assumption.
            * assumption. 
    - destruct HH as [[] | [HH1 HH2]].
        + subst; rewrite H2; reflexivity.
        + apply fresh_nabs in HH1 as []; subst.
            * apply nabs_inv; rewrite HH2; apply perm_action_equal.
            * apply alpha_inv_iff; right; split.
                -- apply fresh_prod_iff; split; [apply name_fresh_iff,name_neq_fresh_iff |]; tauto.
                -- assumption.
Qed.
