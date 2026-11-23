From Nominal Require Import Lambda.

Section Subs.
    Context (a: Name) (N: Λ).

    Definition fvar: Name →ₛ Λ.
       refine (λₛ⟦support a ∪ support N⟧ b, if decide (a = b) then N else Var b).
    Proof.
       intros c d ? ? w; destruct (decide (a = w)); subst.
          - rewrite name_action_neither; [| set_solver | set_solver].
            destruct (decide _); try congruence; rewrite support_spec; set_solver.
          - destruct (decide (c = w)), (decide (d = w)); subst.
            + rewrite !perm_action_equal; unfold action,name_action; rewrite perm_swap_left.
              destruct (decide _); try congruence; reflexivity.
            + rewrite perm_swap_left; destruct (decide _); subst; try congruence; [set_solver |].
              rewrite term_perm_var, perm_swap_right; reflexivity.
            + rewrite perm_swap_right; destruct (decide _); subst; try congruence; [set_solver |].
              rewrite term_perm_var, perm_swap_left; reflexivity.
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
       - intros w z ? ? [b x]; simpl in *; rewrite term_perm_abs, !perm_action_duplicate; reflexivity.
    Defined.

    Fact flam_fcb: ∃ a, a # flam ∧ ∀ x, a # flam (a,x).
    Proof.
       destruct (exist_fresh (support flam ∪ support a ∪ support N)) as [w Hw]; exists w; split.
       - apply support_fresh; set_solver.
       - intros x; destruct (exist_fresh (support flam ∪ support a ∪ support N ∪ support x ∪ support w ∪ support (flam (w, x)) ∪ fv (Lam w x))) as [z Hz].
         exists z; split; [set_solver |].
         rewrite fun_equivar, support_spec; [| set_solver | set_solver].
         rewrite prod_act, perm_swap_left; simpl; symmetry; apply aeq_lam_swap_notin; set_solver.
   Qed.

    Definition subst := alpha_rec (support a ∪ support N) fvar fapp flam ltac:(set_solver) ltac:(set_solver) ltac:(set_solver) flam_fcb.
End Subs.

Notation "M [ a ':=' N ]" := (subst a N M) (at level 1, format "M [ a := N ]").

Lemma subst_var (a b: Name) (m: Λ): (Var b)[a := m] ≡ (if decide (a = b) then m else Var b).
Proof. unfold subst; rewrite alpha_rec_var; unfold fvar; simpl; reflexivity. Qed.

Lemma subst_app (a: Name) (m n t: Λ): (App m n)[a := t] ≡ App (m[a := t]) (n[a := t]).
Proof. unfold subst; rewrite alpha_rec_app; unfold fapp; simpl; reflexivity. Qed.

Lemma subst_lam (a b: Name) (m n: Λ): a ≠ b → a ∉ support n → (Lam a m)[b := n] ≡ Lam a (m[b := n]).
Proof. 
 intros; assert (HH: Lam a (m[b := n]) ≡ flam(a, (m[b := n]))). { simpl; reflexivity. }
 rewrite HH; clear HH; unfold subst; apply alpha_rec_lam. apply not_elem_of_union; split; set_solver.
Qed.

Opaque subst.

Lemma subst_aeq (a: Name) (m p q: Λ): p ≡ q → m[a := p] ≡ m[a := q].
Proof.
   intros; generalize dependent m; set (P := fun t => t[a := p] ≡ t[a := q]).
   apply (alpha_ind (support a ∪ support p ∪ support q) P); subst P; intros; simpl in *.
   - unfold αCompat; intros; rewrite <-H0; auto.
   - rewrite !subst_var; destruct (decide _); auto.
   - rewrite !subst_app; rewrite H0,H1; reflexivity.
   - rewrite !subst_lam; [rewrite H1 | | | |]; set_solver.
Qed.

Lemma subst_neq_var (a: Name) (m n: Λ): a # m → m[a := n] ≡ m.
Proof.
   generalize dependent m; set (P := fun t => a # t → t[a := n] ≡ t). apply (alpha_ind (support a ∪ support n) P); subst P; simpl in *.
   - repeat intro; rewrite <-H; apply H0; rewrite H; auto. 
   - intros b H; rewrite subst_var; apply var_fresh in H; destruct (decide _); subst; try congruence; reflexivity.
   - simpl in *; intros p q ? ? ?; apply app_fresh in H1 as []; rewrite subst_app; rewrite H,H0; auto.
   - simpl in *; intros b m ? ? ?; rewrite subst_lam; [| set_solver | set_solver].
     rewrite H0; [reflexivity | apply lam_fresh in H1 as []; subst; set_solver].
Qed.

Lemma subst_comp (a b: Name) (m p q: Λ): 
   a ≠ b → a ∉ fv p → (m[a := q])[b := p] ≡ (m[b := p])[a := (q[b := p])].
Proof.
   intros; generalize dependent m; set (P := fun t => (t[a := q])[b := p] ≡ (t[b := p])[a := q[b := p]]).
   apply (alpha_ind (support a ∪ support b ∪ support p ∪ support q ∪ support (q[b := p])) P); subst P; simpl in *.
   - unfold αCompat; intros; rewrite <-H1; assumption.
   - intros c; destruct (decide (a = c)), (decide (b = c)); subst; try congruence;
      repeat (rewrite !subst_var; repeat destruct (decide _); subst; try congruence); auto.
      rewrite subst_neq_var; [| apply support_fresh]; auto.
   - intros; rewrite !subst_app; constructor; auto.
   - intros c ? ? ?; rewrite !subst_lam.
     1:(rewrite H2; reflexivity). all:set_solver.
Qed.