From Stdlib Require Import Lists.List.
From Nominal Require Export Nominal Fresh NameAbstraction FreshnessTheorem.
From Nominal.Instances Require Export SupportedFunctions Name Prod Perm.

Inductive Λ : Set :=
| Var: Name → Λ
| App: Λ → Λ → Λ
| Lam: Name → Λ → Λ.

Fixpoint atms (t: Λ) : NameSet :=
  match t with
  | Var a => {[ a ]}
  | App t1 t2 => (atms t1) ∪ (atms t2)
  | Lam a t => {[ a ]} ∪ (atms t)
  end.

Fixpoint term_action (p: Perm) (t: Λ): Λ :=
  match t with
  | Var a => Var (p • a)
  | App m n => App (term_action p m) (term_action p n)
  | Lam a m => Lam (p • a) (term_action p m)
  end.

Instance TermAction: PermAction Λ := term_action.

Lemma term_perm_var p a : p • (Var a) = Var (p • a).
Proof. unfold action; simpl; reflexivity. Qed.

Lemma term_perm_app p m n : p • (App m n) = App (p • m) (p • n).
Proof. unfold action; simpl; reflexivity. Qed.

Lemma term_perm_abs p a m : p • (Lam a m) = Lam (p • a) (p • m).
Proof. unfold action; simpl; reflexivity. Qed.

Section PermTerm.
(* Estes lemas são basicamente demonstrando que Term forma PermT com a igualdade sintática.
  Foram necessários para demonstrar term_perm_alpha, necessário para demonstrar a equivalência
  de alphaCof. *)

Lemma term_perm_proper : Proper ((≡@{Perm}) ==> eq ==> eq) term_action.
Proof.
  repeat intro; unfold equiv,perm_equiv in *; subst.
  induction y0.
  - do 2 rewrite term_perm_var; f_equal; apply H.
  - do 2 rewrite term_perm_app; f_equal; auto.
  - do 2 rewrite term_perm_abs; f_equal; auto.
Qed.

Lemma term_perm_id (t : Λ): ɛ•t = t.
Proof.
  induction t.
  - rewrite term_perm_var; auto.
  - rewrite term_perm_app; rewrite IHt1, IHt2; reflexivity.
  - rewrite term_perm_abs; rewrite IHt; auto.
Qed.

Lemma term_perm_compat p q (t : Λ): p•(q•t) = (q + p)•t.
Proof.
  induction t.
  - repeat rewrite term_perm_var; f_equal; apply gact_compat.
  - repeat rewrite term_perm_app; f_equal; auto.
  - repeat rewrite term_perm_abs; f_equal; [apply gact_compat |]; auto.
Qed. 

Lemma term_perm_swap_distr a b (p : Perm) (x: Λ) : p•⟨a,b⟩•x = ⟨p•a, p•b⟩•p•x.
Proof. rewrite 2term_perm_compat; apply term_perm_proper; auto; apply perm_comm_distr. Qed.

Lemma term_action_neither (a b: Name) (t: Λ) : 
  a ∉ atms t → b ∉ atms t → ⟨a,b⟩•t = t.
Proof.
  induction t; intros.
  - rewrite term_perm_var,name_action_neither; simpl in *; set_solver.
  - rewrite term_perm_app,IHt1,IHt2; simpl in *; set_solver.
  - rewrite term_perm_abs,name_action_neither,IHt; simpl in *; set_solver.
Qed.

Lemma term_action_equal (a : Name) (t: Λ) : 
  ⟨a,a⟩•t = t.
Proof.
  induction t; intros.
  - rewrite term_perm_var,perm_equiv_neutral; f_equal.
  - rewrite term_perm_app,IHt1,IHt2; reflexivity.
  - rewrite term_perm_abs,!perm_equiv_neutral,IHt; reflexivity.
Qed.

Lemma term_action_inv (a b: Name) (t: Λ) : 
  ⟨a,b⟩•t = -⟨a,b⟩•t.
Proof.
  induction t; intros.
  - rewrite !term_perm_var; f_equal.
  - rewrite term_perm_app,IHt1,IHt2; reflexivity.
  - rewrite !term_perm_abs; f_equal.
Qed.

Lemma term_action_swap (a b: Name) (t: Λ) : 
  ⟨a,b⟩•t = ⟨b,a⟩•t.
Proof.
  induction t; intros.
  - rewrite !term_perm_var; f_equal; rewrite swap_perm; reflexivity.
  - rewrite term_perm_app,IHt1,IHt2; reflexivity.
  - rewrite !term_perm_abs; f_equal; [rewrite swap_perm |]; auto.
Qed.

End PermTerm.

(* Inductive aeq: Λ → Λ → Prop :=
| AeqVar: ∀ a, aeq (Var a) (Var a)
| AeqApp: ∀ m m' n n', aeq m m' → aeq n n' → aeq (App m n) (App m' n')
| AeqAbs: ∀ a b m n, 
  (∀ c, c ≠ a → c ≠ b → c ∉ atms m → c ∉ atms n → 
    aeq (⟨a,c⟩•m) (⟨b,c⟩•n)) → aeq (Lam a m) (Lam b n). *)

Reserved Notation "a ≡α b" (at level 61).
Inductive aeqCof: Λ → Λ → Prop :=
| AeqVarC: ∀ a, (Var a) ≡α (Var a)
| AeqAppC: ∀ m m' n n', m ≡α m' → n ≡α n' → (App m n) ≡α (App m' n')
| AeqAbsC: ∀ (L : NameSet) a b m n, (∀ c, c ∉ L → (⟨a,c⟩•m) ≡α (⟨b,c⟩•n)) → (Lam a m) ≡α (Lam b n)
where "a ≡α b" := (aeqCof a b).

Lemma term_perm_alpha p m n: m ≡α n → (p • m) ≡α (p • n).
Proof. 
  induction 1.
  - rewrite term_perm_var; constructor.
  - repeat rewrite term_perm_app; constructor; auto.
  - repeat rewrite term_perm_abs; 
      apply AeqAbsC with (L := ({[a;b]} ∪ (perm_dom p) ∪ L)); intros c Hc.
      rewrite <-(perm_notin_domain_id p c); try set_solver.
      do 2 rewrite <-term_perm_swap_distr; apply H0; set_solver.
Qed.

(* Lemma term_perm_alpha_ a b m n: aeq m n → aeq (⟨a,b⟩•m) (⟨a,b⟩•n).
Proof. Admitted.

Theorem aeqs_equal m n: aeq m n ↔ m ≡α n.
Proof.
  split; intros H.
  - induction H.
    + constructor.
    + constructor; auto. 
    + apply AeqAbsC with (L := ({[a;b]} ∪ (atms m) ∪ (atms n))); intros c Hc.
      apply H0; set_solver.
  - induction H.
    + constructor.
    + constructor; auto.
    + constructor; intros. destruct (exist_fresh ({[a;b;c]} ∪ (atms m) ∪ (atms n) ∪ L)) as [d Hd].
      assert (HH: d ∉ L). { set_solver. } specialize (H0 d HH). Admitted.
      (* apply term_perm_alpha_ with (p := ⟨c,d⟩) in H0.
      rewrite 2(term_perm_swap_distr _ _ ⟨c,d⟩) in H0.
      rewrite name_action_right in H0.
      rewrite 2name_action_neither in H0; [| set_solver | set_solver | set_solver | set_solver].
      assert (HH2 : ⟨ c, d ⟩ • m = m). { apply term_action_neither; set_solver. }
      assert (HH3 : ⟨ c, d ⟩ • n = n). { apply term_action_neither; set_solver. }
      rewrite HH2,HH3 in H0; auto. *)
Qed. *)
    
Instance AeqCofRef: Reflexive aeqCof.
Proof.
  intros t; induction t.
  - constructor.
  - constructor; auto.
  - econstructor; intros; apply term_perm_alpha; eauto.
  Unshelve.
  exact {[t]}. (* anything *)
Qed.

Instance AeqCofSymm: Symmetric aeqCof.
Proof.
  repeat intro; induction H.
  - constructor.
  - constructor; auto.
  - apply AeqAbsC with L; intros; auto.
Qed.

Instance AeqCofRefTrans: Transitive aeqCof.
Proof. 
  repeat intro; generalize dependent z; induction H; auto; intros; inversion H1; subst.
  - constructor; auto.
  - apply AeqAbsC with (L := (L0 ∪ L)); intros; apply H0; set_solver.
Qed.

Instance AeqCofEquiv : Equivalence aeqCof.
Proof. split; typeclasses eauto. Qed.

Instance TermEquiv : Equiv Λ := aeqCof.

Instance TermPermT : PermT Λ.
Proof.
  split.
  - typeclasses eauto.
  - intros p q HPQ x y HXY; unfold equiv,perm_equiv,TermEquiv in *; induction HXY; subst.
    + rewrite !term_perm_var, !HPQ; reflexivity.
    + rewrite !term_perm_app; constructor; auto.
    + rewrite !term_perm_abs; apply AeqAbsC with (L := perm_dom p ∪ perm_dom q ∪ L); intros.
      rewrite <-(perm_notin_domain_id p c) at 1; [| set_solver];
      rewrite <-(perm_notin_domain_id q c) at 2; [| set_solver]; 
      rewrite <-!term_perm_swap_distr; apply H0; set_solver.
  - intros; rewrite term_perm_id; reflexivity.
  - intros; rewrite term_perm_compat; reflexivity.
Qed. 

Fixpoint fv (t: Λ): NameSet :=
  match t with
  | Var a => {[ a ]}
  | App m n => (fv m) ∪ (fv n)
  | Lam a m => (fv m) ∖ {[ a ]}
  end.

Instance TermSupport : Support Λ := fv.

Instance TermNominal : Nominal Λ.
Proof.
  split.
  - exact TermPermT.
  - induction x; intros.
    + rewrite term_perm_var, fresh_fixpoint; try apply support_fresh; set_solver.
    + rewrite term_perm_app; constructor; set_solver.
    + rewrite term_perm_abs; destruct (decide (a = b)); subst.
      * apply AeqAbsC with (L := ∅); intros; rewrite !perm_action_equal; reflexivity.
      * apply AeqAbsC with (L := support a ∪ support b ∪ support t ∪ support x); intros c ?;
        unfold support,TermSupport in H,H0; simpl in *; apply not_elem_of_difference in H,H0; destruct H,H0.
        destruct (decide (a = t)), (decide (b = t)); subst; try congruence.
        -- rewrite name_action_left; rewrite 3IHx; set_solver.
        -- rewrite name_action_right; rewrite !IHx; set_solver.
        -- rewrite name_action_neither, (IHx a b); [reflexivity | | | |]; set_solver.
        -- apply elem_of_singleton in H0; subst; 
           rewrite name_action_right, perm_swap_distr, name_action_left, name_action_neither; [| set_solver | set_solver].
           rewrite IHx, swap_perm; [reflexivity | |]; set_solver.
        -- apply elem_of_singleton in H; subst.
           rewrite name_action_left, perm_swap_distr, name_action_left, name_action_neither; [| set_solver | set_solver].
           rewrite IHx; [reflexivity | |]; set_solver.
        -- apply elem_of_singleton in H0,H; subst; congruence.
Qed.

Instance term_rewrite_var: Proper (eq ==> equiv) (Var).
Proof. repeat intro; rewrite H; reflexivity. Qed.

Instance term_rewrite_app: Proper (equiv ==> equiv ==> equiv) (App).
Proof. repeat intro; apply AeqAppC; auto. Qed.

Instance term_rewrite_lam: Proper (eq ==> equiv ==> equiv) (Lam).
Proof. repeat intro; apply AeqAbsC with (L := ∅); intros; rewrite H; apply perm_inj; assumption. Qed.

Tactic Notation "eabstract" tactic3(tac) :=
let G := match goal with |- ?G => G end in
let pf := constr:(ltac:(tac) : G) in
abstract exact_no_check pf.

Lemma action_var a b c: ⟨a,b⟩ • Var c = Var (⟨a,b⟩•c).
Proof. unfold action; simpl; reflexivity. Qed.

Lemma action_lam a b c t: ⟨a,b⟩ • Lam c t = Lam (⟨a,b⟩•c) (⟨a,b⟩•t).
Proof. unfold action; simpl; reflexivity. Qed.

Lemma action_app a b m n: ⟨a,b⟩ • App m n = App (⟨a,b⟩•m) (⟨a,b⟩•n).
Proof. unfold action; simpl; reflexivity. Qed.

Lemma perm_var p a : p • Var a = Var (p • a).
Proof. unfold action; simpl; reflexivity. Qed.

Lemma perm_app p m n: p • App m n = App (p•m) (p•n).
Proof. unfold action; simpl; reflexivity. Qed.

Lemma perm_lam p a t: p • (Lam a t) = Lam (p•a) (p•t).
Proof. unfold action; simpl; reflexivity. Qed.

Lemma var_fresh (a b: Name): a # Var b → a ≠ b.
Proof. 
   intros; apply some_any_iff in H; unfold freshP_a in H; 
   destruct (exist_fresh (support a ∪ support b ∪ support (Var b))) as [w Hw];
   specialize (H w ltac:(set_solver)); destruct (decide (a = b)); subst.
   - rewrite perm_var,perm_swap_left in H; inversion H; subst; set_solver.
   - auto.
Qed.

Lemma app_fresh (a: Name) (m n: Λ): a # App m n → a # m ∧ a # n.
Proof.
   intros; apply some_any_iff in H; unfold freshP_a in H.
   destruct (exist_fresh (support a ∪ support m ∪ support n ∪ support (App m n))) as [w Hw].
   specialize (H w ltac:(set_solver)); rewrite perm_app in H; inversion H; subst; split;
   exists w; split; set_solver.
Qed.

Lemma term_lam_alpha_equiv (a b: Name) (m n: Λ): 
   Lam a m ≡ Lam b n ↔ ⟦a⟧m ≡ ⟦b⟧n.
Proof.
   split; intros.
   - inversion H; subst; apply alpha_inv_iff; destruct (decide (a = b)); subst.
      + left; split; auto; destruct (exist_fresh L) as [w Hw]; apply (perm_inj _ _ ⟨b,w⟩).
        apply H1; assumption.
      + right.
        assert (HH: a#n). {
            destruct (exist_fresh (support a ∪ support b ∪ support m ∪ support n ∪ L)) as [w [[[[]%not_elem_of_union ?]%not_elem_of_union ?]%not_elem_of_union ?]%not_elem_of_union].
            assert (HH1: ⟨w,b⟩•⟨w,b⟩•n ≡ n). { apply perm_action_duplicate; reflexivity. }
            assert (HH2: ⟨w,b⟩•⟨w,a⟩•w = a). { rewrite perm_swap_left, perm_swap_neither; auto; apply not_eq_sym,name_neq_fresh_iff,support_fresh; assumption. }
            rewrite <-HH1; specialize (H1 w ltac:(assumption)). rewrite (swap_perm b w) in H1.
            rewrite <-HH2,<-H1. rewrite (swap_perm a w). do 2! apply fresh_equivariant; apply support_fresh; assumption.
         }
        split; [apply fresh_prod_iff; split |].
        * apply support_fresh; set_solver.
        * assumption.
        * destruct (exist_fresh (support a ∪ support b ∪ support m ∪ support n ∪ L)) as [w [[[[]%not_elem_of_union ?]%not_elem_of_union ?]%not_elem_of_union ?]%not_elem_of_union].
           specialize (H1 w ltac:(assumption)); apply (perm_inj _ _ ⟨a,w⟩).
           rewrite perm_swap_distr,perm_swap_left,(perm_swap_neither b a w),(fresh_fixpoint a w n),(swap_perm w b).
           assumption.
           assumption.
           apply support_fresh; assumption.
           set_solver.
           set_solver.
   - apply alpha_inv_iff in H as [[] | []]; subst.
      + apply AeqAbsC with (L := ∅); intros; apply perm_inj; assumption.
      + apply AeqAbsC with (L := support a ∪ support b ∪ support m ∪ support n); intros.
        apply (perm_inj _ _ ⟨a,c⟩).
        rewrite perm_action_duplicate,perm_swap_distr,perm_swap_neither,perm_swap_right,(fresh_fixpoint a c n),(swap_perm b a).
        assumption.
        apply fresh_prod_iff in H as []; assumption.
        apply support_fresh; set_solver.
        apply fresh_prod_iff in H as []. apply name_neq_fresh_iff in H. auto.
        set_solver.
Qed.

Lemma lam_fresh (a b: Name) (m: Λ): b # Lam a m → a = b ∨ (a ≠ b ∧ b # m).
Proof.
   intros; destruct (decide (a = b)); subst.
   - left; reflexivity.
   - right; split; auto.
     destruct (exist_fresh (support a ∪ support b ∪ support m ∪ support (Lam a m))) as [w Hw].
     exists w; split.
     + set_solver.
     + apply some_any_iff in H; unfold freshP_a in H; specialize (H w ltac:(set_solver)).
       rewrite perm_lam,perm_swap_neither in H.
       * apply term_lam_alpha_equiv,alpha_inv_name_equiv_iff in H; assumption.
       * assumption.
       * set_solver.
Qed.

Lemma aeq_lam_swap_notin (a b: Name) (t: Λ) : 
  b ∉ fv (Lam a t) → Lam a t ≡ Lam b (⟨a,b⟩•t).
Proof.
  intros; simpl in *; apply not_elem_of_difference in H as []; apply term_lam_alpha_equiv.
  - apply alpha_rename,support_fresh; assumption.
  - apply elem_of_singleton in H; subst; rewrite term_action_equal; reflexivity.
Qed.  

Section InductionAlpha. (* COPELLO's *)

Definition αCompat (P: Λ → Prop): Prop := ∀ m n, m ≡ n → P m → P n.

Local Lemma perm_ind:
  ∀ P: Λ → Prop, αCompat P →
    (∀ t, P (Var t)) →
    (∀ m n, P m → P n → P (App m n)) →
    (∀ a m, (∀ p, P (p • m)) → P (Lam a m)) →
    ∀ t, P t.
Proof.
  intros P Compat Hvar Happ Hlam t.
  apply (Compat (ɛ • t) _ (gact_id t)).
  apply (@Λ_ind (fun t => ∀ p, P (p • t))).
    + intros; rewrite perm_var; apply Hvar.
    + intros; rewrite perm_app; apply Happ; auto.
    + intros a m H p; rewrite perm_lam; apply Hlam; intros.
      eapply (Compat ((p + p0) • m)). 
      * rewrite gact_compat; reflexivity.
      * apply H.
Qed.

Local Lemma lam_rename (L: NameSet):
  ∀ P: Λ → Prop, αCompat P →
      (∀ b m, b ∉ L → (∀ p, P (p • m)) → P (Lam b m)) →
      ∀ a m, (∀ p, P (p • m)) → P (Lam a m).
Proof.
  intros P Compat HLam a m Hp. set (c := fresh (support (Lam a m) ∪ L)).
  apply (Compat (Lam c (⟨a,c⟩•m))).
  - symmetry. apply aeq_lam_swap_notin. subst c; unfold support, TermSupport; simpl.
    eapply not_elem_of_weaken; [eapply is_fresh | set_solver].
  - apply HLam.
    + subst c. eapply not_elem_of_weaken; [eapply is_fresh | set_solver].
    + intros; eapply (Compat ((⟨a,c⟩ + p) • m)).
      * rewrite gact_compat; reflexivity.
      * apply Hp.
Qed.

Definition alpha_ind (L: NameSet) :
  ∀ P: Λ → Prop, αCompat P →
    (∀ a, P (Var a)) →
    (∀ m n, P m → P n → P (App m n)) →
    (∀ a m, a ∉ L → P m → P (Lam a m)) →
    ∀ m, P m.
Proof.
  intros P Compat Hvar Happ HLam.
  apply perm_ind.
  - apply Compat.
  - apply Hvar.
  - apply Happ.
  - apply (lam_rename L); auto.
    intros b m HbL HP; apply HLam.
    + assumption.
    + apply (Compat (ɛ • m)); [apply gact_id | apply HP].
Qed.

End InductionAlpha.

Section RecursionAlpha.
Context `{Nominal X} (L : NameSet).
Context (fvar : Name →ₛ X) (fapp : (X * X) →ₛ X) (flam : (Name * X) →ₛ X).
Context (fvarL : f_supp fvar ⊆ L) (fappL : f_supp fapp ⊆ L) (flamL : f_supp flam ⊆ L).
Context (fcb: (∃ a, a # flam ∧ ∀ x, a # flam (a,x))).

  Local Lemma fcb_some_any:
    (∀ a, a # flam → ∀ x, a # (flam (a,x))) ↔ (∃ a, a # flam ∧ ∀ x, a # (flam (a,x))).
  Proof.
    clear fcb; split; intros.
    - destruct (exist_fresh (support flam)) as [w Hw]; exists w; split.
      + apply support_fresh; assumption.
      + apply H1, support_fresh; auto.
    - destruct H1 as [w [H1w H2w]]; destruct (decide (a = w)).
      + subst; auto.
      + specialize (H2w (⟨a,w⟩•x)). apply (fresh_equivariant ⟨a,w⟩) in H2w.
        rewrite perm_swap_right,fun_equivar,prod_act,perm_swap_right,
                fresh_fixpoint,perm_action_duplicate in H2w; assumption.
  Qed.

  Local Lemma alpha_flam_equiv (a b: Name) (x y: X): 
    a # flam → b # flam → ⟦a⟧x ≈α ⟦b⟧y → flam (a,x) ≡ flam (b,y).
  Proof.
    intros. 
    destruct (exist_fresh (support a ∪ support b ∪ support x ∪ support y ∪ support flam ∪ support (flam (a,x)) ∪ support (flam (b,y)))) as [c ?].
    apply not_elem_of_union in H4 as [[[[[[]%not_elem_of_union ?]%not_elem_of_union ?]%not_elem_of_union ?]%not_elem_of_union ?]%not_elem_of_union ?].
    rewrite <-(fresh_fixpoint c a (flam (a,x))), <-(fresh_fixpoint c b (flam (b,y))); auto.
    rewrite !fun_equivar, !(fresh_fixpoint _ _ flam), !prod_act, !perm_swap_right; try (apply fsupp_equiv); try auto.
    unfold equiv,prod_equiv,prod_relation; simpl; split.
      + reflexivity.
      + apply alpha_some_any in H3; apply H3; repeat split; apply support_fresh; auto.
      + apply support_fresh; assumption.
      + apply support_fresh; assumption.
      + apply support_fresh; assumption.
      + eapply fcb_some_any in fcb; eauto.
      + apply support_fresh; assumption.
      + eapply fcb_some_any in fcb; eauto.
  Qed.

  Lemma perm_swap_equal (a b: Name) (x: X): ⟨a,b⟩ • x ≡ ⟨b,a⟩ • x.
  Proof. rewrite swap_perm; reflexivity. Qed.

  Definition _flam : [𝔸]X →ₛ X.
    refine (
      λₛ⟦support flam⟧ (ax: [𝔸]X), 
        let h: Name →ₛ X := λₛ⟦support (ax.(name)) ∪ support (ax.(term)) ∪ support flam⟧ c, 
        (flam (c, ⟨ax.(name),c⟩ • ax.(term))) in freshF h
    ).
  Proof.
    all: swap 1 2.
    - intros w z Hw Hz [a x]; unfold freshF.
      set (g := (λₛ⟦_⟧ c : Name, flam (c, ⟨name (⟨w,z⟩ • ⟦a⟧x),c⟩ • term (⟨w,z⟩ • ⟦a⟧x)))).
      set (h := (λₛ⟦_⟧ c : Name, flam (c, ⟨name ⟦a⟧x,c⟩ • term ⟦a⟧x))).
      destruct (exist_fresh (L ∪ support flam ∪ support w ∪ support z ∪ support x ∪ support h ∪ support g)) as [c Hc].
      erewrite (freshness_theorem_inj g _ (fresh (support g)) c), (freshness_theorem_inj h _ (fresh (support h)) c);
      try (apply fresh_support_fresh); try (apply support_fresh; set_solver).
      subst g h; simpl.
      rewrite fun_equivar, support_spec, !prod_act; auto.
      assert (HH: ∀ (a b c : Name), perm_swap ⟨a,b⟩ c = ⟨a,b⟩ • c). { intros; unfold action, name_action; reflexivity. }
      rewrite perm_swap_distr. rewrite (HH w z c), (HH w z (⟨w,z⟩ • a)).
      rewrite !perm_action_duplicate, !(name_action_neither w z c). reflexivity. 
      apply not_elem_of_union in Hc as [[[[[? ?]%not_elem_of_union ?]%not_elem_of_union ?]%not_elem_of_union ?]%not_elem_of_union ?].
      apply name_neq_fresh_iff, support_fresh; assumption.
      apply not_elem_of_union in Hc as [[[[[? ?]%not_elem_of_union ?]%not_elem_of_union ?]%not_elem_of_union ?]%not_elem_of_union ?].
      apply name_neq_fresh_iff, support_fresh; assumption.
    - intros x y Hxy; unfold freshF; cbn zeta; set (w := fresh _); set (z := fresh _).
      set (g := (λₛ⟦ _ ⟧ c : Name, flam (c, ⟨name x,c⟩ • term x))).
      set (h := (λₛ⟦ _ ⟧ c : Name, flam (c, ⟨name y,c⟩ • term y))).
      destruct x as [a x]; destruct y as [b y].
      destruct (exist_fresh (L ∪ support flam ∪ support w ∪ support z ∪ support h ∪ support g ∪ support x ∪ support y)) as [c Hc].
      erewrite (freshness_theorem_inj g _ w c), (freshness_theorem_inj h _ z c);
      try (apply fresh_support_fresh); try (apply support_fresh; set_solver).
      simpl. apply not_elem_of_union in Hc as [[[[[[[]%not_elem_of_union ?]%not_elem_of_union ?]%not_elem_of_union ?]%not_elem_of_union ?]%not_elem_of_union ?]%not_elem_of_union ?].
      apply alpha_flam_equiv; try (apply support_fresh; assumption).
      pose proof (@Equivalence_Transitive _ _ alpha_equivalence_e) as T; pose proof (@Equivalence_Symmetric _ _ alpha_equivalence_e) as S.
      transitivity (⟦a⟧x). symmetry. apply alpha_rename, support_fresh; assumption.
      transitivity (⟦b⟧y). apply Hxy. apply alpha_rename, support_fresh; assumption.
    Unshelve.
      + simpl; destruct (exist_fresh (support g ∪ support flam)) as [k Hk]; exists k; split.
        * apply support_fresh; set_solver.
        * eapply fcb_some_any in fcb; eauto; apply support_fresh; set_solver. 
      + simpl; destruct (exist_fresh (support h ∪ support flam)) as [k Hk]; exists k; split.
        * apply support_fresh; set_solver.
        * eapply fcb_some_any in fcb; eauto; apply support_fresh; set_solver.
      + typeclasses eauto.
      + typeclasses eauto.
      + typeclasses eauto.
      + assumption.
      + typeclasses eauto.
      + intros w z Hw Hz c.
        rewrite <-(fresh_fixpoint w z flam) at 2;  try (apply support_fresh; set_solver).
        rewrite fsupp_action, <-perm_inv, prod_act. apply gact_proper. reflexivity.
        apply fsupp_equiv. unfold equiv,prod_equiv,prod_relation; simpl; split.
        * reflexivity.
        * assert (HH: ∀ (a b c : Name), perm_swap ⟨a,b⟩ c = ⟨a,b⟩ • c). { intros; unfold action, name_action; reflexivity. }
          rewrite perm_swap_distr, (HH w z (name ax)), (HH w z c).
          rewrite (name_action_neither w z (name ax)), (support_spec (term ax) w z).
          reflexivity. set_solver. set_solver. 
          symmetry. apply name_neq_fresh_iff, support_fresh. set_solver. 
          symmetry. apply name_neq_fresh_iff, support_fresh. set_solver.
      + simpl; destruct (exist_fresh (support g ∪ support flam)) as [k Hk]; exists k; split.
        * apply support_fresh; set_solver.
        * eapply fcb_some_any in fcb; eauto; apply support_fresh; set_solver.
      + simpl; destruct (exist_fresh (support h ∪ support flam)) as [k Hk]; exists k; split.
        * apply support_fresh; set_solver.
        * eapply fcb_some_any in fcb; eauto; apply support_fresh; set_solver.
  Defined.

  Section _flamProperties.

  Local Lemma flam_abs_eq_flam_support: support flam = support _flam.
  Proof. reflexivity. Qed.

  (* TODO: Better name *)
  Local Lemma efs (a: Name): a ∉ support flam → ∀ x: X, flam (a,x) ≡ _flam ⟦a⟧x.
  Proof. 
    intros. simpl. set (w := fresh _). apply alpha_flam_equiv.
    - apply support_fresh; assumption.
    - subst w; unfold support; simpl; apply support_fresh; apply not_elem_of_weaken with (Y := name_support a ∪ Spt x ∪ fun_supp_support flam).
      apply is_fresh. set_solver.
    - apply alpha_rename, support_fresh; subst w; unfold support; simpl.
      apply not_elem_of_weaken with (Y := name_support a ∪ Spt x ∪ fun_supp_support flam).
      apply is_fresh. set_solver.
  Qed.

  Local Lemma ft_flam (Fm: Perm →ₛ X) (a: Name) (p: Perm) (Sp: NameSet): 
    ∃ c: Name, (c ∉ Sp) ∧ c # _flam ⟦c⟧(Fm (⟨a,c⟩ + p)).
  Proof.
    destruct (exist_fresh (Sp ∪ support _flam)) as [w Hw]; exists w; split.
    - apply not_elem_of_union in Hw as []; assumption.
    - rewrite <-efs; rewrite <-flam_abs_eq_flam_support in *.
      + destruct (exist_fresh (support flam)) as [d Hd].
        rewrite <-(fresh_fixpoint d w flam),fsupp_action,<-perm_inv,prod_act,name_action_right.
        pose proof fcb_some_any as []. specialize (H2 fcb). apply support_fresh in Hd.
        specialize (H2 d Hd (⟨d,w⟩•(Fm (⟨a,w⟩ + p)))).
        apply (fresh_equivariant ⟨d,w⟩) in H2; rewrite perm_swap_left in H2.
        apply H2.
        apply support_fresh; auto.
        apply support_fresh; apply not_elem_of_union in Hw as []; assumption.
      + apply not_elem_of_union in Hw as []; assumption.
  Qed.

  End _flamProperties.

  Opaque _flam. (* Don't look inside _flam *)

  Definition g_var (a: Name): Perm →ₛ X.
    refine (λₛ⟦L ∪ support a⟧ p : Perm, fvar (p • a)).
  Proof.
    - intros ? ? HH; rewrite HH; reflexivity.
    - intros w z []%not_elem_of_union []%not_elem_of_union p;
      unfold action at 3; unfold PermActionPerm;
      rewrite <-2!gact_compat, <-perm_inv, (fresh_fixpoint _ _ a);
        try (apply support_fresh; assumption);
        rewrite perm_inv at 2; rewrite <-fsupp_action, fresh_fixpoint;
          try (apply support_fresh; set_solver); reflexivity.
  Defined.

  Definition g_app (Fm Fn: Perm →ₛ X): Perm →ₛ X.
    refine (λₛ⟦L ∪ support Fm ∪ support Fn⟧ p, fapp (Fm p, Fn p)).
  Proof.
    - intros ? ? HH; rewrite HH; reflexivity.
    - intros w z [[]%not_elem_of_union]%not_elem_of_union [[]%not_elem_of_union]%not_elem_of_union p.
      rewrite <-(fresh_fixpoint w z Fm) at 1; try (apply support_fresh; set_solver);
      rewrite <-(fresh_fixpoint w z Fn) at 1; try (apply support_fresh; set_solver);
      rewrite <-2!fun_equivar, <-prod_act; rewrite perm_inv at 2; rewrite <-fsupp_action;
      rewrite fresh_fixpoint; try (apply support_fresh; set_solver); reflexivity.
  Defined.

  Definition g_lam (a: Name) (m: Λ) (Fm: Perm →ₛ X): Perm →ₛ X.
    refine (
      λₛ⟦ L ∪ support a ∪ support (Fm) ⟧ p,
        let h: Name →ₛ X := λₛ⟦L ∪ support _flam ∪ support a ∪ support m ∪ support (Fm) ∪ support p⟧ a', 
          (_flam ⟦a'⟧(Fm (⟨a,a'⟩ + p))) in freshF h
    ).
    all: swap 1 2.
    - intros w z Hw Hz p; unfold freshF; cbn zeta.
      set (g := (λₛ⟦ _ ⟧ a' : Name, _flam ⟦a'⟧(Fm (⟨ a, a' ⟩ + (⟨ w, z ⟩ • p))))).
      set (h := (λₛ⟦ _ ⟧ a' : Name, _flam ⟦a'⟧(Fm (⟨ a, a' ⟩ + p)))).
      destruct (exist_fresh (L ∪ support _flam ∪ support a ∪ support m ∪ support (Fm) ∪ support w ∪ support z ∪ support (⟨ w, z ⟩ • p) ∪ support p)) as [b Hb].
      erewrite (freshness_theorem_inj g _ (fresh (support g)) b), (freshness_theorem_inj h _ (fresh (support h)) b);
      try (apply fresh_support_fresh); try (apply support_fresh; subst h g; unfold support at 1; simpl; split_union; repeat (apply not_elem_of_union; split; try eauto)).
      (* all: swap 1 2. all: swap 2 3; try (subst; simpl; apply ft_flam). *)
      subst g h; simpl.
      assert (HH: _flam ⟦b⟧(Fm (⟨a,b⟩+(⟨w,z⟩•p))) ≡ _flam ⟦b⟧((⟨w,z⟩•(Fm)) (⟨w,z⟩•⟨a,b⟩+p))). {
      apply fsupp_equiv, nabs_inv;
      rewrite perm_distr_1, perm_distr,<-(fresh_fixpoint w z (Fm)) at 1;
      try reflexivity; try (apply support_fresh).
      apply not_elem_of_union in Hw as [[]%not_elem_of_union ?]; assumption.
      apply not_elem_of_union in Hz as [[]%not_elem_of_union ?]; assumption.
      apply not_elem_of_union in Hw as [[]%not_elem_of_union ?]; apply name_neq_fresh_iff, support_fresh; assumption.
      apply not_elem_of_union in Hb as [[[[]%not_elem_of_union ?]%not_elem_of_union ?]%not_elem_of_union ?]; symmetry; apply name_neq_fresh_iff, support_fresh; assumption.
      apply not_elem_of_union in Hz as [[]%not_elem_of_union ?]; apply name_neq_fresh_iff, support_fresh; assumption.
      apply not_elem_of_union in Hb as [[[]%not_elem_of_union ?]%not_elem_of_union ?]; symmetry; apply name_neq_fresh_iff, support_fresh; assumption.
      } rewrite HH; clear HH.
      rewrite <-(fresh_fixpoint w z b) at 1.
      all: swap 1 2.
      apply not_elem_of_union in Hb as [[[[]%not_elem_of_union ?]%not_elem_of_union ?]%not_elem_of_union ?]; apply name_fresh_iff, support_fresh; assumption.
      all: swap 1 2.
      apply not_elem_of_union in Hb as [[[]%not_elem_of_union ?]%not_elem_of_union ?]; apply name_fresh_iff, support_fresh; assumption.
      assert (HH: _flam ⟦⟨w,z⟩•b⟧((⟨w,z⟩•(Fm)) (⟨w,z⟩•⟨a,b⟩+p)) ≡ _flam (⟦⟨w,z⟩•b⟧(⟨w,z⟩•(Fm (⟨a,b⟩+p))))). {
      apply fsupp_equiv, nabs_inv; rewrite fun_equivar; reflexivity.
      } rewrite HH; clear HH.
      rewrite <-nabs_action,<-fsupp_action, fresh_fixpoint. reflexivity.
      apply not_elem_of_union in Hw as [[]%not_elem_of_union ?]; apply support_fresh; rewrite <-flam_abs_eq_flam_support.
      apply not_elem_of_weaken with L; assumption.
      apply not_elem_of_union in Hz as [[]%not_elem_of_union ?]; apply support_fresh; rewrite <-flam_abs_eq_flam_support.
      apply not_elem_of_weaken with L; assumption.
    - intros x y Hxy; unfold freshF; cbn zeta; set (a' := fresh _); set (b' := fresh _);
      set (g := (λₛ⟦ _ ⟧ _ : Name, _flam ⟦_⟧(Fm (⟨ a, _ ⟩ + x))));
      set (h := (λₛ⟦ _ ⟧ _' : Name, _flam ⟦_⟧(Fm (⟨ a, _ ⟩ + y))));
      destruct (exist_fresh (L ∪ support _flam ∪ support a ∪ support m ∪ support (Fm) ∪ support x ∪ support y ∪ support a' ∪ support b')) as [c Hc];
      erewrite (freshness_theorem_inj g _ a' c), (freshness_theorem_inj h _ b' c);
      try (apply fresh_support_fresh); try (apply support_fresh; subst h g; unfold support at 1; simpl; split_union; repeat (apply not_elem_of_union; split; try eauto)).
      simpl; apply fsupp_equiv, nabs_inv, fsupp_equiv, grp_op_proper; auto.
  Unshelve.
      (* Make these proof terms opaque to reduce term size. *)
      eabstract(
        intros w z Hw Hz b;
        apply not_elem_of_union in Hw as [[[[[]%not_elem_of_union ?]%not_elem_of_union ?]%not_elem_of_union ?]%not_elem_of_union ?];
        apply not_elem_of_union in Hz as [[[[[]%not_elem_of_union ?]%not_elem_of_union ?]%not_elem_of_union ?]%not_elem_of_union ?];
        rewrite <-(fresh_fixpoint w z _flam) at 2; try (apply support_fresh; assumption);
        rewrite fsupp_action, <-perm_inv, nabs_action; apply gact_proper, fsupp_equiv; auto;
        rewrite (fun_equivar (⟨w,z⟩) (Fm)), (fresh_fixpoint w z (Fm)); try (apply support_fresh; assumption);
        rewrite perm_distr_3; try (apply name_neq_fresh_iff, support_fresh); try assumption; reflexivity).
      eabstract(
        simpl; destruct (exist_fresh (support g ∪ support flam)) as [k []%not_elem_of_union]; exists k; split;
        [apply support_fresh; assumption | pose proof fcb_some_any as [? hh]; specialize (hh fcb); rewrite <-efs; [eapply hh; apply support_fresh; assumption | assumption]]
      ).
      eabstract(
        simpl; destruct (exist_fresh (support h ∪ support flam)) as [k []%not_elem_of_union]; exists k; split;
        [apply support_fresh; assumption | pose proof fcb_some_any as [? hh]; specialize (hh fcb); rewrite <-efs; [eapply hh; apply support_fresh; assumption | assumption]]
      ).
      eabstract(
        simpl; destruct (exist_fresh (support g ∪ support flam)) as [k []%not_elem_of_union]; exists k; split;
        [apply support_fresh; assumption | pose proof fcb_some_any as [? hh]; specialize (hh fcb); rewrite <-efs; [eapply hh; apply support_fresh; assumption | assumption]]
      ).
      eabstract(
        simpl; destruct (exist_fresh (support h ∪ support flam)) as [k []%not_elem_of_union]; exists k; split;
        [apply support_fresh; assumption | pose proof fcb_some_any as [? hh]; specialize (hh fcb); rewrite <-efs; [eapply hh; apply support_fresh; assumption | assumption]]
      ).
  Defined.

  Fixpoint perm_alpha_rec (t: Λ): Perm →ₛ X :=
  match t with
    | Var a => g_var a
    | App m n => g_app (perm_alpha_rec m) (perm_alpha_rec n)
    | Lam a m => g_lam a m (perm_alpha_rec m)
  end.

  Lemma perm_alpha_rec_var (a: Name):
    perm_alpha_rec (Var a) = g_var a.
  Proof. simpl; reflexivity. Qed.

  Lemma perm_alpha_rec_app (m n: Λ):
    perm_alpha_rec (App m n) = g_app (perm_alpha_rec m) (perm_alpha_rec n).
  Proof. simpl; reflexivity. Qed.

  Lemma perm_alpha_rec_lam (a: Name) (m: Λ):
    perm_alpha_rec (Lam a m) = g_lam a m (perm_alpha_rec m).
  Proof. simpl; reflexivity. Qed.

  Lemma alpha_rec_perm (t: Λ):
    ∀ (p q: Perm), perm_alpha_rec t (q + p) ≡ perm_alpha_rec (q • t) p.
  Proof. 
    induction t; intros.
    - simpl; rewrite gact_compat; reflexivity.
    - simpl; rewrite IHt1,IHt2; reflexivity.
    - Opaque freshF. rewrite perm_lam; simpl.
      set (f := λₛ⟦ _ ⟧ a' : Name, _flam ⟦_⟧(_)); set (g := λₛ⟦ _ ⟧ a' : Name, _flam ⟦_⟧(_)).
      destruct (exist_fresh (support f ∪ support g ∪ support q)) as [w [[]%not_elem_of_union]%not_elem_of_union].
      erewrite <-!(freshness_theorem _ _ w); try (apply support_fresh; auto).
      simpl; apply fsupp_equiv,nabs_inv.
      rewrite grp_assoc,perm_comm_distr,(perm_notin_domain_id _ w),<-grp_assoc,IHt; try reflexivity.
      auto. Unshelve.
      + subst f; simpl. pose proof (ft_flam (perm_alpha_rec t0) t (q + p) (L ∪ support _flam ∪ support t ∪ support t0 ∪ support (perm_alpha_rec t0) ∪ support (q + p))) as [w' []]. 
        exists w'. split.
        * apply support_fresh; unfold support. simpl. auto.
        * auto.
      + subst g; simpl. pose proof (ft_flam (perm_alpha_rec (q • t0)) (q•t) p (L ∪ support _flam ∪ support (q • t) ∪ support (q • t0) ∪ support (perm_alpha_rec (q • t0)) ∪ support p)) as [w' []].
        exists w'. split.
        * apply support_fresh; unfold support; simpl; auto.
        * auto.
      Transparent freshF.
  Qed.
  
(* perhaps can be made simpler *)
  Theorem perm_alpha_rec_respectfull (m n: Λ):
    m ≡α n → perm_alpha_rec m ≡ perm_alpha_rec n.
  Proof.
    induction 1.
    - simpl; unfold g_var; reflexivity.
    - simpl; unfold g_app; unfold equiv, fun_supp_equiv; intro p; simpl. rewrite IHaeqCof1, IHaeqCof2; reflexivity.
    - simpl; unfold g_lam, equiv, fun_supp_equiv; intros p; simpl.
      set (s1 := L ∪ support _flam ∪ support a ∪ support m ∪ support (perm_alpha_rec m) ∪ support p);
      set (s2 := L ∪ support _flam ∪ support b ∪ support n ∪ support (perm_alpha_rec n) ∪ support p).
      set (h1 := (λₛ⟦ s1 ⟧ a' : Name, _flam ⟦a'⟧(perm_alpha_rec m (⟨ a, a' ⟩ + p))));
      set (h2 := (λₛ⟦ s2 ⟧ a' : Name, _flam ⟦a'⟧(perm_alpha_rec n (⟨ b, a' ⟩ + p)))).
      assert (HH1: _flam ⟦fresh (support h1)⟧(perm_alpha_rec m (⟨ a, fresh (support h1) ⟩ + p)) = h1 (fresh (support h1))).
      { subst h1 s1; reflexivity. }
      assert (HH2: _flam ⟦fresh (support h2)⟧(perm_alpha_rec n (⟨ b, fresh (support h2) ⟩ + p)) = h2 (fresh (support h2))).
      { subst h2 s2; reflexivity. }
      rewrite HH1, HH2; clear HH1 HH2.
      destruct (exist_fresh (L0 ∪ support h2 ∪ support h1)) as [w Hw].
      erewrite (freshness_theorem_inj h1 _ (fresh (support h1)) w), (freshness_theorem_inj h2 _ (fresh (support h2)) w).
      + subst h1 h2; simpl; apply fsupp_equiv; rewrite !alpha_rec_perm.
        apply name_abstraction_inv; left; split; auto.
        rewrite H2. reflexivity. apply not_elem_of_union in Hw as [[]%not_elem_of_union]. assumption.
      + apply fresh_support_fresh. 
      + apply support_fresh. apply not_elem_of_union in Hw as [[]%not_elem_of_union]. assumption.
      + apply fresh_support_fresh. 
      + apply support_fresh. apply not_elem_of_union in Hw as [[]%not_elem_of_union]. assumption.
  Unshelve.
      simpl; destruct (exist_fresh (support h1 ∪ support flam)) as [k []%not_elem_of_union]; exists k; split;
        [apply support_fresh; assumption | pose proof fcb_some_any as [? hh]; specialize (hh fcb); rewrite <-efs; [eapply hh; apply support_fresh; assumption | assumption]].
      simpl; destruct (exist_fresh (support h2 ∪ support flam)) as [k []%not_elem_of_union]; exists k; split;
        [apply support_fresh; assumption | pose proof fcb_some_any as [? hh]; specialize (hh fcb); rewrite <-efs; [eapply hh; apply support_fresh; assumption | assumption]].
  Qed.

  Instance: Proper (aeqCof ==> equiv) (perm_alpha_rec).
  Proof. repeat intro; apply perm_alpha_rec_respectfull; assumption. Qed.

  Lemma perm_alpha_rec_supported (a b: Name) (t: Λ):
    ∀ p: Perm, a ∉ (L ∪ support p) → b ∉ (L ∪ support p) → ⟨a,b⟩•(perm_alpha_rec (⟨a,b⟩•t)) p ≡ perm_alpha_rec t p.
  Proof.
    set (P := fun t => ∀ p : Perm, a ∉ (L ∪ support p) → b ∉ (L ∪ support p) → ⟨ a, b ⟩ • perm_alpha_rec (⟨ a, b ⟩ • t) p ≡ perm_alpha_rec t p).
    apply (alpha_ind (L ∪ support a ∪ support b) P); subst P.
    - repeat intro. pose proof perm_alpha_rec_respectfull. unfold equiv,fun_supp_equiv in H5.
      transitivity (⟨ a, b ⟩ • perm_alpha_rec (⟨ a, b ⟩ • m) p).
      + apply perm_inj; apply H5,term_perm_alpha; symmetry; assumption.
      + transitivity (perm_alpha_rec m p). apply H2; assumption. apply H5. assumption. 
    - simpl; intros x p ? ?. rewrite not_elem_of_union in H1,H2. destruct H1,H2. rewrite fun_equivar, support_spec. rewrite perm_comm,perm_action_duplicate. reflexivity.
      + assumption.
      + assumption.
      + eapply not_elem_of_weaken. eapply H1. assumption.
      + eapply not_elem_of_weaken. eapply H2. assumption.
    - intros m n IHt1 IHt2. Opaque perm_alpha_rec. simpl in *. Transparent perm_alpha_rec.
      intros p ? ?. rewrite action_app,perm_alpha_rec_app. simpl.
      rewrite fun_equivar, support_spec, prod_act. apply fsupp_equiv. split; simpl; auto.
      + apply not_elem_of_union in H1 as []; apply not_elem_of_weaken with (Y := L). auto. assumption.
      + apply not_elem_of_union in H2 as []; apply not_elem_of_weaken with (Y := L). auto. assumption.
    - intros c m Sc. Opaque perm_alpha_rec. simpl. Transparent perm_alpha_rec.
      intros IHt p aL bL.
      rewrite perm_lam,!perm_alpha_rec_lam; unfold g_lam.
      Opaque freshF. simpl. Transparent freshF.
      set (h := λₛ⟦ _ ⟧ a' : Name, _flam ⟦a'⟧(perm_alpha_rec (⟨ a, b ⟩ • m) (⟨ ⟨ a, b ⟩ • c, a' ⟩ + p))).
      set (g := λₛ⟦ _ ⟧ a' : Name, _flam ⟦a'⟧(perm_alpha_rec m (⟨ c, a' ⟩ + p))).
      unfold freshF.
      destruct (exist_fresh (support g ∪ support h ∪ support a ∪ support b)) as [w Hw].
      erewrite (freshness_theorem_inj h _ (fresh (support h)) w), (freshness_theorem_inj g _ (fresh (support g)) w).
      + simpl; rewrite fun_equivar, support_spec, nabs_action, support_spec.
        apply fsupp_equiv,nabs_inv. rewrite name_action_neither. apply IHt.
        * apply not_elem_of_union in aL as []; apply not_elem_of_union; split. assumption. apply notin_support_comp_perm. split.
          -- apply notin_support_comp_swap. split.
            ++ apply not_elem_of_union in Sc as [[]%not_elem_of_union ?]. set_solver.
            ++ apply not_elem_of_union in Hw as [[[]%not_elem_of_union ?]%not_elem_of_union ?]. set_solver.
          -- assumption.
        * apply not_elem_of_union in bL as []; apply not_elem_of_union; split. assumption. apply notin_support_comp_perm. split.
          -- apply notin_support_comp_swap. split.
            ++ apply not_elem_of_union in Sc as [[]%not_elem_of_union ?]. set_solver.
            ++ apply not_elem_of_union in Hw as [[[]%not_elem_of_union ?]%not_elem_of_union ?]. set_solver.
          -- assumption.
        * apply not_elem_of_union in Sc as [[]%not_elem_of_union ?]. set_solver.
        * apply not_elem_of_union in Sc as [[]%not_elem_of_union ?]. set_solver. 
        * apply not_elem_of_union in Hw as [[[]%not_elem_of_union ?]%not_elem_of_union ?]. set_solver.
        * apply not_elem_of_union in Hw as [[[]%not_elem_of_union ?]%not_elem_of_union ?]. set_solver.
        * apply not_elem_of_union in aL as []; apply not_elem_of_weaken with (Y := L). auto. assumption.
        * apply not_elem_of_union in bL as []; apply not_elem_of_weaken with (Y := L). auto. assumption.
      + apply fresh_support_fresh.
      + apply not_elem_of_union in Hw as [[[]%not_elem_of_union ?]%not_elem_of_union ?]. apply support_fresh. set_solver.
      + apply fresh_support_fresh.
      + apply not_elem_of_union in Hw as [[[]%not_elem_of_union ?]%not_elem_of_union ?]. apply support_fresh. set_solver.
  Unshelve.
    simpl; destruct (exist_fresh (support h ∪ support flam)) as [k []%not_elem_of_union]; exists k; split;
        [apply support_fresh; assumption | pose proof fcb_some_any as [? hh]; specialize (hh fcb); rewrite <-efs; [eapply hh; apply support_fresh; assumption | assumption]].
    simpl; destruct (exist_fresh (support g ∪ support flam)) as [k []%not_elem_of_union]; exists k; split;
        [apply support_fresh; assumption | pose proof fcb_some_any as [? hh]; specialize (hh fcb); rewrite <-efs; [eapply hh; apply support_fresh; assumption | assumption]].
  Qed.

  Definition alpha_rec: Λ →ₛ X. refine (λₛ⟦L⟧ t, perm_alpha_rec t ɛ).
  Proof.
    - repeat intro; apply perm_alpha_rec_respectfull; assumption.
    - intros; apply perm_alpha_rec_supported; rewrite support_empty; set_solver.
  Defined.

  Lemma alpha_rec_respectfull (m n: Λ) : 
    m ≡α n → alpha_rec m ≡ alpha_rec n.
  Proof. intros; unfold alpha_rec; simpl; apply perm_alpha_rec_respectfull; assumption. Qed.

  Lemma alpha_rec_var (a: Name) : 
    alpha_rec (Var a) = fvar a.
  Proof. unfold alpha_rec; simpl; rewrite gact_id; auto. Qed.
  
  Lemma alpha_rec_app (m n: Λ):
    alpha_rec (App m n) = fapp (alpha_rec m, alpha_rec n).
  Proof. unfold alpha_rec; simpl; reflexivity. Qed.

  Lemma alpha_rec_lam (a: Name) (t: Λ): 
    a ∉ L → alpha_rec (Lam a t) ≡ flam (a, alpha_rec t).
  Proof.
    intros; unfold alpha_rec; simpl; rewrite efs; [| set_solver]; set (s := fresh _); apply fsupp_equiv.
    apply name_abstraction_inv; right; assert (HH: s ∉ (L ∪ support flam ∪ support a ∪ support t ∪ support (perm_alpha_rec t) ∪ support ɛ@{Perm})). { apply is_fresh. } split.
      + apply fresh_nabs; right; split.
        * apply not_elem_of_union in HH as [[[[]%not_elem_of_union ?]%not_elem_of_union ?]%not_elem_of_union ?]. set_solver.
        * apply fresh_fun_supp.
          -- apply support_fresh; unfold support, fun_supp_support; simpl; apply not_elem_of_union in HH as [[[[]%not_elem_of_union ?]%not_elem_of_union ?]%not_elem_of_union ?]. assumption.
          -- apply support_fresh; unfold support, fun_supp_support; simpl; apply not_elem_of_union in HH as [[[[]%not_elem_of_union ?]%not_elem_of_union ?]%not_elem_of_union ?]. assumption.
      + rewrite alpha_rec_perm. assert (HHH: ∀ t, perm_alpha_rec t ɛ = alpha_rec t). { intros. reflexivity. }
        rewrite !HHH, fun_equivar. rewrite (support_spec alpha_rec),swap_perm. reflexivity.
        * unfold alpha_rec, support, fun_supp_support; simpl.
          apply not_elem_of_union in HH as [[[[[]%not_elem_of_union ?]%not_elem_of_union ?]%not_elem_of_union ?]%not_elem_of_union ?]. assumption.
        * unfold alpha_rec, support, fun_supp_support; simpl. assumption.
  Qed.

End RecursionAlpha.
