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

Instance name_abstraction_support `{Nominal X}: Support [𝔸]X := λ a, support (abs a).

Lemma fresh_pair1 `{Nominal X} (a b: name) (x: X): a # (b, x) → a ≠ b ∧ a # x.
Proof.
    intros [w []];(*  destruct (exist_fresh (support b ∪ support x ∪ support (b,x))) as [w ?]; apply some_any_iff in Hf.
    cut (w ∉ support (b, x)); [intros HH | set_solver]; specialize (Hf w HH); *)
    unfold support,prod_support,action,prod_act,equiv,prod_equiv,prod_relation in *; simpl in *;
    destruct H2; split.
    - unfold action, name_action in H2; simpl in *; try repeat case_decide; subst.
        + destruct_notin_union; support_fresh_tac; apply name_fresh_neq in H1; congruence.
        + destruct_notin_union; exfalso; apply H1; set_solver.
        + assumption.
    - exists w; split; auto; destruct_notin_union; auto.
Qed.

Instance name_abstraction_nominal `{Nominal X}: Nominal [𝔸]X.
Proof. split.
    - exact name_abstraction_perm.
    - intros [[a x]] b c ? ?; destruct (decide (b = c)), (decide (b = a)), (decide (c = a)); 
        subst; try (congruence || apply perm_action_equal); unfold support, name_abstraction_support in *; simpl in *.
        + apply support_fresh,fresh_pair1 in H1 as []; congruence.
        + apply support_fresh,fresh_pair1 in H2 as []; congruence.
        + new w fresh (⟨b,c⟩ ∙ a) a (⟨b,c⟩ ∙ x) x; exists w; split; simpl; [intuition |];
          rewrite swap_perm_neither, (fresh_fixpoint b c x); auto; apply fresh_pair1 in H1,H2; intuition.
Qed.

(* Basic properties *)
Lemma nabs_action `{Nominal X} p a x: p ∙ [a]x = [p ∙ a](p ∙ x).
Proof. auto. Qed.

Lemma nabs_support `{Nominal X} a x: support [a]x = support a ∪ support x.
Proof. auto. Qed.

Lemma nabs_equiv_name_eq `{Nominal X} a x x': [a]x ≡ [a]x' → x ≡ x'.
Proof. intros HH; unfold equiv, name_abstraction_equiv in HH; apply alpha_inv1 in HH; auto. Qed.

Lemma fresh_pair2 `{Nominal X} (a b: name) (x: X): a ≠ b → a # x → a # (b, x).
Proof.
    intros; destruct (exist_fresh (support a ∪ support b ∪ support x ∪ support (b, x))) as [w ?]; exists w; split.
    - set_solver.
    - unfold action, equiv, prod_act, prod_equiv, prod_relation; split; simpl; apply fresh_fixpoint; auto.
        + apply name_neq_fresh_iff; auto.
        + destruct_notin_union; support_fresh_tac; auto.
        + destruct_notin_union; support_fresh_tac; auto.
Qed.

Lemma fresh_pair_iff `{Nominal X} (a b: name) (x: X): a ≠ b ∧ a # x ↔ a # (b, x).
Proof. split; intros.
    - apply fresh_pair2; intuition.
    - apply fresh_pair1; intuition.
Qed. 

(* Lemma fresh_equiv `{Nominal X} a (x x': X): x ≡ x' → a # x → a # x'.
Proof. 
    intros. rewrite <-H1. 
    intros Heq Hf; destruct (exist_fresh (support a ∪ support x ∪ support x')) as [w ?]; exists w; split;
    [| apply some_any_iff in Hf; rewrite <-Heq; apply Hf]; set_solver.
Qed. *)

Lemma alpha_equiv_neq `{Nominal X} a a' x x': (a,x) ≈α (a',x') ↔ (a = a' ∧ x ≡ x') ∨ (a # (a',x') ∧ x ≡ ⟨a,a'⟩ ∙ x').
Proof.
    destruct (decide (a = a')); subst.
    - split. 
        + intros HH; apply alpha_inv1 in HH; left; intuition.
        + intros [[] | []]; apply alpha_inv1.
            * auto.
            * rewrite <-(perm_action_equal a' x'); auto.
    - split.
        + intros [b []]; right.
            assert (Hfp: a # (a', x')). {
               apply fresh_pair2; auto.
               cut (⟨b,a'⟩ ∙ ⟨b,a'⟩ ∙ x' ≡ x'); [intros HH1 | apply perm_action_duplicate].
               cut (⟨b,a'⟩ ∙ ⟨b,a⟩ ∙ b = a); [intros HH2 | rewrite swap_perm_left, swap_perm_neither; auto; apply not_eq_sym, name_neq_fresh_iff; intuition].
               rewrite <-HH1, <-H2; rewrite <-HH2 at 1; do 2 apply fresh_equivariant; intuition.
            }
            split.
            * assumption. 
            * apply fresh_pair1 in Hfp as []; rewrite (perm_expand _ b _), <-!gact_compat.
               rewrite (fresh_fixpoint a b x'); auto. rewrite <-H2, perm_swap; symmetry; apply perm_action_duplicate.
               intuition. apply not_eq_sym. auto. apply not_eq_sym. apply name_neq_fresh_iff. intuition.
        + intros [[] | ]; try congruence; destruct H1. apply fresh_pair1 in H1 as [].
            new w fresh a a' x x'. exists w; split; [intuition |]. rewrite H2. rewrite (perm_expand w a a'), <-!gact_compat.
            * rewrite (fresh_fixpoint w a x'); auto.
            * apply not_eq_sym, name_neq_fresh_iff; intuition.
            * apply not_eq_sym. assumption.
Qed.

(* Lemma fresh_nabs `{Nominal X} (a b: name) (x: X): a # [b]x → a ≠ b ∧ a # x.
Proof.
    intros [w []]; unfold support,name_abstraction_support,action,equiv,name_abstraction_equiv,name_abstraction_action in *; simpl in *.
    apply alpha_equiv_neq in H2; destruct H2.
    - destruct H2; split.
        + unfold action, name_action in H2; simpl in *; try repeat case_decide; subst.
            * unfold support, prod_support in *; set_solver.
            * assumption.
            * assumption.
        + exists w; split; unfold support, prod_support in *; [set_solver |]; auto.
    - destruct H2; split.
        + unfold action,name_action in H2; simpl in *; try repeat case_decide; subst.
            * rewrite swap_perm_left in H3.           
    intros [w []];(*  destruct (exist_fresh (support b ∪ support x ∪ support (b,x))) as [w ?]; apply some_any_iff in Hf.
    cut (w ∉ support (b, x)); [intros HH | set_solver]; specialize (Hf w HH); *)
    unfold support,prod_support,action,prod_act,equiv,prod_equiv,prod_relation in *; simpl in *;
    destruct H2; split.
    - unfold action, name_action in H2; simpl in *; try repeat case_decide; subst.
        + destruct_notin_union; support_fresh_tac; apply name_fresh_neq in H1; congruence.
        + destruct_notin_union; exfalso; apply H1; set_solver.
        + assumption.
    - exists w; split; auto; destruct_notin_union; auto.
Qed. *)

(* Lemma nabs_equiv_neq `{Nominal X} a a' x x': [a]x ≡ [a']x' ↔ (a = a' ∧ x ≡ x') ∨ (a # [a']x' ∧ x ≡ ⟨a,a'⟩ ∙ x').
Proof. 
    split; intros.
    - unfold equiv, name_abstraction_equiv in *; simpl in *; apply alpha_equiv_neq in H1 as [].
        + left; assumption.
        + right; destruct H1; split.
            * destruct H1 as [w []]; exists w; split.
                -- unfold support, name_abstraction_support in *; simpl in *; set_solver.
                -- unfold action,prod_act,name_abstraction_action in *; simpl in *; unfold equiv, prod_equiv,prod_relation in *; simpl in *.
                    destruct H3. apply alpha_inv2; auto.
            * assumption.
    - destruct H1.
        + destruct H1; unfold equiv, name_abstraction_equiv; simpl; apply alpha_inv2; auto.
        + destruct H1. new w fresh a a' x x'. exists w; split.
            * intuition.
            * rewrite (perm_expand w a a'), <-!gact_compat.   
    
    

            unfold equiv, name_abstraction_equiv; simpl. , name_abstraction_action; simpl.  

    - intros HH; destruct (decide (a = a')); subst.
        + apply nabs_equiv_name_eq in HH; left; intuition.
        + right; unfold equiv, name_abstraction_equiv in HH; 
          destruct (exist_fresh (support a ∪ support a' ∪ support x ∪ support x' ∪ support ([a']x'))) as [w ?]; split.
            * exists w; split; [set_solver |]; rewrite nabs_action, swap_perm_neither; [| set_solver | set_solver];
                unfold equiv, name_abstraction_equiv; apply alpha_equiv_some_any in HH.
                destruct (exist_fresh (support a ∪ support a' ∪ support x ∪ support x' ∪ support ([a']x') ∪ support (⟨ a, w ⟩ ∙ x'))) as [z ?];
                cut (w #( a, a', x, x')); [intro wF |].
                -- specialize (HH w wF); exists z; split; [destruct_notin_union; support_fresh_tac; intuition |].
                    set (L := ⟨ z, a' ⟩ ∙ ⟨ a, w ⟩ ∙ x'). rewrite (perm_expand z w a'); subst L.
                exists z; split.
                cut (w #( a, a', x, x')); [intro wF |].
                -- destruct (exist_fresh (support a ∪ support a' ∪ support x ∪ support x' ∪ support ([a']x') ∪ support (⟨ a, w ⟩ ∙ x'))) as [z ?];
                   specialize (HH z wF); exists w; split. 
                
                specialize (HH w).     *)

Lemma lol `{Nominal} a a' x: a' # [a]x ↔ a = a' ∨ a' # x.  
Proof.
    split; intros.
    - destruct (decide (a = a')); subst.
        + left. auto.
        + right; destruct (exist_fresh (support a ∪ support a' ∪ support x ∪ support [a]x)) as [w ?].
            exists w; split; [set_solver |]; apply some_any_iff in H1; cut (w ∉ support [a]x); [intros I | set_solver];
            specialize (H1 w I); unfold equiv,name_abstraction_equiv in H1; simpl in H1.
            assert (L: ⟨ a', w ⟩ ∙ a = a). { rewrite swap_perm_neither; auto; apply not_eq_sym,name_neq_fresh_iff; destruct_notin_union; support_fresh_tac; auto. }
            rewrite L in H1; apply alpha_inv1 in H1; assumption.
    - assert (L: a = a' → a' # [a]x). {
        intros; subst; destruct (exist_fresh (support a' ∪ support x)) as [w ?]; exists w; split.
        * auto.
        * unfold equiv, name_abstraction_equiv; simpl; rewrite swap_perm_left; apply alpha_equiv_neq; right; split.
            -- apply fresh_pair_iff; split; destruct_notin_union; support_fresh_tac; [apply name_neq_fresh_iff |]; auto.
            -- rewrite perm_swap; auto.
    } destruct H1.
        + auto. 
        + destruct (decide (a = a')); subst.
            * auto. 
            * clear L; destruct (exist_fresh (support a ∪ support a' ∪ support x)) as [w ?]; exists w; split.   
                -- unfold support, name_abstraction_support, support, prod_support; simpl; set_solver. 
                -- unfold equiv, name_abstraction_equiv; simpl; rewrite swap_perm_neither; auto.
                    ++ apply alpha_inv2; auto; apply fresh_fixpoint; auto; destruct_notin_union; support_fresh_tac; auto.
                    ++ apply not_eq_sym, name_fresh_neq; destruct_notin_union; support_fresh_tac; auto. 
Qed.
    