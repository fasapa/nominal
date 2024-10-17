From Nominal Require Import Lambda.

Section Subs.
    Context (a: Name) (N: Λ).

    Instance: Proper (eq ==> equiv) (Var).
    Proof. repeat intro; rewrite H; reflexivity. Qed.

    Instance: Proper (equiv ==> equiv ==> equiv) (App).
    Proof. repeat intro; apply AeqAppC; auto. Qed.

    Definition S: NameSet := support a ∪ support N.

    Definition fvar: Name →ₛ Λ.
       refine (λₛ⟦S⟧ b, if decide (a = b) then N else Var b).
    Proof.
       intros c d ? ? w. destruct (decide (a = w)); subst.
          - rewrite name_action_neither.
            + destruct (decide _); try congruence; rewrite support_spec; set_solver.
            + set_solver.
            + set_solver.
          - destruct (decide (c = w)), (decide (d = w)); subst.
            + rewrite !perm_action_equal; unfold action,name_action; rewrite perm_swap_left.
              destruct (decide _); try congruence; reflexivity.
            + rewrite perm_swap_left; destruct (decide _); subst; try congruence.
               * set_solver.
               * rewrite term_perm_var, perm_swap_right; reflexivity.
            + rewrite perm_swap_right; destruct (decide _); subst; try congruence.
               * set_solver.
               * rewrite term_perm_var, perm_swap_left; reflexivity.
            + rewrite perm_swap_neither; try destruct (decide _); subst; try congruence.
              rewrite term_perm_var,perm_swap_neither; set_solver.
    Defined.

    Definition fapp: (Λ * Λ) →ₛ Λ.
       refine (λₛ⟦∅⟧ mn, App (fst mn) (snd mn)).
    Proof.
       - intros [] [] [H1 H2]; simpl in *; rewrite H1,H2; reflexivity.
       - intros c d ? ? [x y]; simpl; rewrite term_perm_app, !perm_action_duplicate; reflexivity. 
    Defined.

    Definition flam: (Name * Λ) →ₛ Λ.
       refine (λₛ⟦∅⟧ am, Lam (fst am) (snd am)).
    Proof.
       - intros [b x] [c y] [H1 H2]; simpl in *; apply AeqAbsC with (L := ∅); intros d ?; rewrite H1; 
         apply term_perm_alpha; assumption.
       - intros w z ? ? [b x]; simpl in *; rewrite term_perm_abs, !perm_action_duplicate; apply AeqAbsC with (L := ∅).
         intros ? ?; rewrite !perm_action_duplicate; reflexivity.
    Defined.

    Fact fvarL: f_supp fvar ⊆ S. Proof. set_solver. Qed.
    Fact fappL: f_supp fapp ⊆ S. Proof. set_solver. Qed.
    Fact flamL: f_supp flam ⊆ S. Proof. set_solver. Qed.

    Fact fcb: ∃ a, a # flam ∧ ∀ x, a # flam (a,x).
    Proof.
       destruct (exist_fresh (support flam ∪ support a ∪ support N)) as [w Hw].
       exists w; split.
       - apply support_fresh; set_solver.
       - intros x. destruct (exist_fresh (support flam ∪ support a ∪ support N ∪ support x ∪ support w ∪ support (flam (w, x)) ∪ fv (Lam w x))) as [z Hz].
         exists z; split.
         + set_solver.
         + rewrite fun_equivar, support_spec.
           * rewrite prod_act, perm_swap_left; simpl; symmetry; apply aeq_lam_swap_notin; set_solver.
           * set_solver.
           * set_solver.
    Qed.

    Definition subst := alpha_rec (support a ∪ support N) fvar fapp flam fvarL fappL flamL fcb.

End Subs.

Notation " '[' a ':=' N ']' M " := (subst a N M) (at level 59, M at next level, format "[ a  :=  N ] M").

Lemma subst_var (a b: Name) (m: Λ): [a := m](Var b) ≡ (if decide (a = b) then m else Var b).
Proof. unfold subst; rewrite alpha_rec_var; unfold fvar; simpl; reflexivity. Qed.

Lemma subst_app (a: Name) (m n t: Λ): [a := t](App m n) ≡ App ([a := t]m) ([a := t]n).
Proof. unfold subst; rewrite alpha_rec_app; unfold fapp; simpl; reflexivity. Qed.

Lemma subst_lam (a b: Name) (m n: Λ): a ≠ b → a ∉ support n → [b := n](Lam a m) ≡ Lam a ([b := n]m).
Proof. 
 intros; assert (HH: Lam a ([b := n]m) ≡ flam(a, ([b := n]m))). { simpl; reflexivity. }
 rewrite HH; clear HH; unfold subst; apply alpha_rec_lam; apply not_elem_of_union; split; set_solver.
Qed.