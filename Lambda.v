From Nominal Require Import Nominal Fresh Alpha NameAbstraction.
From Nominal Require Import Instances.Name.

Require Import FunInd.

Inductive Term : Set :=
| Var: Name → Term
| App: Term → Term → Term
| Lam: Name → Term → Term.

Fixpoint atms (t: Term) : NameSet :=
  match t with
  | Var a => {[ a ]}
  | App t1 t2 => (atms t1) ∪ (atms t2)
  | Lam a t => {[ a ]} ∪ (atms t)
  end.

Fixpoint term_action (p: Perm) (t: Term): Term :=
  match t with
  | Var a => Var (p • a)
  | App m n => App (term_action p m) (term_action p n)
  | Lam a m => Lam (p • a) (term_action p m)
  end.

Instance TermAction: PermAction Term := term_action.

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

Lemma term_perm_id (t : Term): ɛ•t = t.
Proof.
  induction t.
  - rewrite term_perm_var; auto.
  - rewrite term_perm_app; rewrite IHt1, IHt2; reflexivity.
  - rewrite term_perm_abs; rewrite IHt; auto.
Qed.

Lemma term_perm_compat p q (t : Term): p•(q•t) = (q + p)•t.
Proof.
  induction t.
  - repeat rewrite term_perm_var; f_equal; apply gact_compat.
  - repeat rewrite term_perm_app; f_equal; auto.
  - repeat rewrite term_perm_abs; f_equal; [apply gact_compat |]; auto.
Qed. 

Lemma term_perm_swap_distr a b (p : Perm) (x: Term) : p•⟨a,b⟩•x = ⟨p•a, p•b⟩•p•x.
Proof. rewrite 2term_perm_compat; apply term_perm_proper; auto; apply perm_comm_distr. Qed.

Lemma term_action_neither (a b: Name) (t: Term) : 
  a ∉ atms t → b ∉ atms t → ⟨a,b⟩•t = t.
Proof.
  induction t; intros.
  - rewrite term_perm_var,name_action_neither; simpl in *; set_solver.
  - rewrite term_perm_app,IHt1,IHt2; simpl in *; set_solver.
  - rewrite term_perm_abs,name_action_neither,IHt; simpl in *; set_solver.
Qed.

Lemma term_action_equal (a : Name) (t: Term) : 
  ⟨a,a⟩•t = t.
Proof.
  induction t; intros.
  - rewrite term_perm_var,perm_equiv_neutral; f_equal.
  - rewrite term_perm_app,IHt1,IHt2; reflexivity.
  - rewrite term_perm_abs,!perm_equiv_neutral,IHt; reflexivity.
Qed.

End PermTerm.

(* Inductive aeq: Term → Term → Prop :=
| AeqVar: ∀ a, aeq (Var a) (Var a)
| AeqApp: ∀ m m' n n', aeq m m' → aeq n n' → aeq (App m n) (App m' n')
| AeqAbs: ∀ a b m n, 
  (∀ c, c ≠ a → c ≠ b → c ∉ atms m → c ∉ atms n → 
    aeq (⟨a,c⟩•m) (⟨b,c⟩•n)) → aeq (Lam a m) (Lam b n). *)

Inductive aeqCof: Term → Term → Prop :=
| AeqVarC: ∀ a, aeqCof (Var a) (Var a)
| AeqAppC: ∀ m m' n n', aeqCof m m' → aeqCof n n' → aeqCof (App m n) (App m' n')
| AeqAbsC: ∀ (L : NameSet) a b m n, 
  (∀ c, c ∉ L → aeqCof (⟨a,c⟩•m) (⟨b,c⟩•n)) → aeqCof (Lam a m) (Lam b n).

(* Lemma term_perm_alpha_ p m n: aeq m n → aeq (p • m) (p • n).
Proof. 
  induction 1.
  - rewrite term_perm_var; constructor.
  - repeat rewrite term_perm_app; constructor; auto.
  - repeat rewrite term_perm_abs; constructor; intros. *)


Lemma term_perm_alpha p m n: aeqCof m n → aeqCof (p • m) (p • n).
Proof. 
  induction 1.
  - rewrite term_perm_var; constructor.
  - repeat rewrite term_perm_app; constructor; auto.
  - repeat rewrite term_perm_abs; 
      apply AeqAbsC with (L := ({[a;b]} ∪ (perm_dom p) ∪ L)); intros c Hc.
      rewrite <-(perm_notin_domain_id p c); try set_solver.
      do 2 rewrite <-term_perm_swap_distr; apply H0; set_solver.
Qed.

(* Theorem aeqs_equal m n: aeq m n <-> aeqCof m n.
Proof.
  split; induction 1.
  - constructor.
  - constructor; auto.
  - apply AeqAbsC with (L := ({[a;b]} ∪ (atms m) ∪ (atms n))); intros c Hc;
    apply H0; set_solver.
  - constructor.
  - constructor; auto.
  - constructor; intros; destruct (exist_fresh ({[a;b;c]} ∪ (atms m) ∪ (atms n) ∪ L)) as [d Hd].
    assert (HH: d ∉ L). { set_solver. } specialize (H0 d HH).
    apply (term_perm_alpha_ (⟨c,d⟩)) in H0. 
    rewrite 2(term_perm_swap_distr _ _ ⟨c,d⟩) in H0.
    rewrite name_action_right in H0.
    rewrite 2name_action_neither in H0; [| set_solver | set_solver | set_solver | set_solver].
    assert (HH2 : ⟨ c, d ⟩ • m = m). { apply term_action_neither; set_solver. }
    assert (HH3 : ⟨ c, d ⟩ • n = n). { apply term_action_neither; set_solver. }
    rewrite HH2,HH3 in H0; auto.
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

Instance TermEquiv : Equiv Term := aeqCof.

Instance TermPermT : PermT Term.
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

Fixpoint fv (t: Term): NameSet :=
  match t with
  | Var a => {[ a ]}
  | App m n => (fv m) ∪ (fv n)
  | Lam a m => (fv m) ∖ {[ a ]}
  end.

Instance TermSupport : Support Term := fv.

Instance TermNominal : Nominal Term.
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

(* Definition term_rect_general := fun (P : Term → Type)
  (fvar : ∀ a : Name, P (Var a))
  (fapp : ∀ t1: Term, P t1 → ∀ t2: Term, P t2 → P (App t1 t2))
  (flam : ∀ a : Name, ∀ t: Term, P t → P (Lam (a,t))) =>
  fix F (t: Term) : P t :=
    match t as t' return (P t') with
    | Var a => fvar a
    | App t1 t2 => fapp t1 (F t1) t2 (F t2)
    | Lam (a, t) => flam a t (F t)
    end. *)

(* Definition term_rec_general (P : Term → Set) := term_rect_general P.
Definition term_ind_general (P : Term → Prop) := term_rect_general P. *)

(* Fixpoint atm (t: Term) : NameSet.
Proof.
  apply term_rec_general.
  - exact (λ a, {[ a ]}).
  - exact (λ _ fm _ fn, fm ∪ fn).
  - exact (λ a _ fm, {[ a ]} ∪ fm).
  - exact t.
Defined. *)

(* 
Definition subst_name (c a b: Name): Name :=
  if Atom.dec c b then a else c.

Lemma subst_neq (a b c: Name) : c ≠ b → subst_name c a b = c.
Proof. intros; unfold subst_name; destruct Atom.dec; subst; [congruence | reflexivity]. Qed.

Lemma subst_eq (a b c: Name) : c = b → subst_name c a b = a.
Proof. intros; unfold subst_name; destruct Atom.dec; subst; [reflexivity | congruence]. Qed.

Fixpoint subst (t: Term) (a b: Name) : Term :=
  match t with
  | Var c => Var (subst_name c a b)
  | App t1 t2 => App (subst t1 a b) (subst t2 a b)
  | Lam (c,t) => Lam ((subst_name c a b), (subst t a b))
  end.

Lemma subst_notin_atm t a b: b ∉ atm t → subst t a b = t.
Proof. induction t using term_ind_general; intros; simpl in *.
  - rewrite subst_neq; [reflexivity | set_solver].
  - rewrite IHt1, IHt2; set_solver.
  - rewrite IHt.
    + rewrite subst_neq; [reflexivity | set_solver].
    + set_solver.  
Qed.

Lemma subst_equal m a: subst m a a = m.
Proof. 
  induction m using term_ind_general; intros; simpl in *. 
  - destruct (decide (a0 = a)); [rewrite subst_eq | rewrite subst_neq]; subst; auto.
  - rewrite IHm1, IHm2; reflexivity.
  - destruct (decide (a0 = a)); [rewrite subst_eq | rewrite subst_neq]; 
      subst; try rewrite IHm; auto.
Qed.

Lemma subst_var a b c : a = c → subst (Var a) b c = Var b.
Proof. intros; simpl; rewrite subst_eq; auto. Qed.

Lemma subst_var_neq a b c : a ≠ c → subst (Var a) b c = Var a.
Proof. intros; simpl; rewrite subst_neq; auto. Qed.

Inductive aeq: Term → Term → Prop :=
| AeqVar: ∀ a, aeq (Var a) (Var a)
| AeqApp: ∀ m n m' n', aeq m m' → aeq n n' → aeq (App m n) (App m' n')
| AeqAbs: ∀ (a b: Name) (m n: Term), 
    (∀ c, c ≠ a → c ≠ b → c ∉ atm m → c ∉ atm n → aeq (subst m c a) (subst n c b)) → 
    aeq (Lam (a,m)) (Lam (b,n)).

Lemma aeq_subst_notin: ∀ m n a c, 
  c ∉ atm m → c ∉ atm n → aeq m n → aeq (subst m a c) (subst n a c).
Proof. intros; do 2 (try rewrite subst_notin_atm); auto. Qed.

Lemma aeq_subst: ∀ m n a c, 
  aeq m n → aeq (subst m a c) (subst n a c).
Proof.
  intros; inversion H.
  - destruct (decide (a0 = c)); [rewrite subst_var | rewrite subst_var_neq]; auto; constructor.
  - admit.
  - simpl; constructor; intro w; intros.
    destruct (decide (a0 = b)); subst.
    +    
   destruct (decide (a0 = c)), (decide (b = c)); subst.
    + rewrite subst_eq; auto. specialize (H0 a).
      
     apply H0.

Instance subst_proper: Proper (aeq ==> eq ==> eq ==> aeq) subst.
Proof. repeat intro; subst. apply aeq_subst; auto.

#[export] Instance: Equiv Term := aeq.
#[export] Instance: Reflexive aeq.
Proof.
  intro x; induction x using term_ind_general.
  - constructor.
  - constructor; auto.
  - destruct (exist_fresh ({[a]} ∪ (atm1 x))) as [c Hc]; apply AeqAbs with (c := c).
    + split; set_solver.
    + split; set_solver. 
    + apply aeq_subst; set_solver.
Qed.

#[export] Instance: Symmetric aeq.
Proof.
  repeat intro; induction H.
  - constructor.
  - constructor; auto.
  - econstructor; [destruct H; split; eauto | intuition | auto].
Qed.

#[export] Instance: Transitive aeq.
Proof. Admitted.

#[export] Instance: Equivalence aeq.
Proof. split; typeclasses eauto. Qed.

#[export] Instance: Equiv Term := aeq. *)

(* Fixpoint taction (p: Perm) (t: Term): Term :=
  match t with
  | Var a => Var (p • a)
  | App m n => App (taction p m) (taction p n)
  | Lam (a,m) => Lam ((p • a), (taction p m))
  end. *)

(* #[export] Instance: PermT Term.
Proof.
  split.
  - typeclasses eauto.
  - intros p q PEq m n TEq; (* rewrite PEq *)
    unfold equiv, perm_equiv, Equiv_instance_1 in *.
    unfold action, PermAction_instance_0 in *.
    induction TEq; simpl.
    + rewrite PEq. reflexivity.
    + constructor; auto.
    + econstructor.
      * (* facil, basta pegar um C diferente *) admit.
      * (* facil, basta pegar um C diferente *) admit.
      * (* algume lema que relacione action e subst. *) admit.
  - intro t; induction t using term_ind_general; unfold action, PermAction_instance_0 in *;
    simpl.
    + rewrite gact_id; reflexivity.
    + constructor; [rewrite IHt1 | rewrite IHt2]; reflexivity.
    + rewrite gact_id. econstructor.
      * admit.
      * admit.
      * unfold action, PermAction_instance_0 in *; simpl; rewrite IHt; reflexivity.
  - intros p q t; induction t using term_ind_general; unfold action, PermAction_instance_0 in *;
    simpl.
    + rewrite gact_compat; reflexivity.
    + constructor; auto.
    + rewrite gact_compat; econstructor.
      * admit.
      * admit.
      * rewrite IHt; reflexivity.      
Admitted. *)

(* #[export] Instance TermNominal: Nominal Term.
Proof. split.
    - typeclasses eauto.
    - intros t a b Sa Sb;
      unfold action, TermAction, support, TermSupport,
                equiv, TermEquiv in *.
      induction t; simpl in *.
      + rewrite support_spec; auto; reflexivity.
      + constructor; [apply IHt1 | apply IHt2]; set_solver. 
      + admit.
Admitted. *)
      (* + apply not_elem_of_difference in Sa, Sb; destruct Sa, Sb.
        * econstructor; admit. (* a ∉ fv t ∧ b ∉ fv t*)
        * econstructor; admit. (* a ∉ fv t ∧ b = a0 *)
        * econstructor; admit. (* a = a0 ∧ b ∉ fv t*)
        * econstructor; admit. a = a0 ∧ b = a0 *)

From Nominal.Instances Require Import SupportedFunctions Name Prod Perm.

Section FreshnessTheorem.
  Context `{Nominal X} (h: Name →ₛ X).
  
  Definition freshF : X := h (fresh (support h)).

  Lemma freshness_theorem_some_any :
    (∃ a, a # h ∧ a # (h a)) ↔ (∀ a, a # h → a # (h a)).
  Proof.
    split; intros HH.
    - intros a AH; destruct HH as [b [BH1 BH2]]; destruct (decide (a = b)).
      + subst; assumption.
      + apply (fresh_equivariant ⟨a,b⟩) in BH2; 
        rewrite perm_swap_right,fun_equivar,perm_swap_right,fresh_fixpoint in BH2; assumption.
    - new c fresh h; exists c; split.
      + apply support_fresh; assumption.
      + apply HH, support_fresh; assumption.
  Qed.

  Theorem freshness_theorem (Haf: ∃ a, a # h ∧ a # (h a)) :
    ∀ a, a # h → (h a) ≡ freshF.
  Proof.
    intros a AH; unfold freshF; set (a' := fresh _); destruct (decide (a = a')); subst; try reflexivity.
    rewrite <-(fresh_fixpoint a a' (h a')), fun_equivar,perm_swap_right,fresh_fixpoint.
      + reflexivity.
      + assumption.
      + apply fresh_support_fresh.
      + apply fresh_fun_supp; [| apply name_neq_fresh_iff]; assumption.
      + apply freshness_theorem_some_any; [| apply fresh_support_fresh]; assumption.
  Qed.

  Corollary freshness_theorem2 :
    ∀ a b, (∃ (c: Name), c ∉ support h ∧ c # (h c)) → a # h → b # h → h a ≡ h b.
  Proof. 
    intros; rewrite !freshness_theorem; try reflexivity; try assumption;
    destruct H1 as [x ?]; exists x; split; try (apply support_fresh; tauto); tauto.
  Qed.

End FreshnessTheorem.

(* Definition FCB `{Nominal X, Nominal Y} (f: X →ₛ Y) :=
  { a | a ∉ (support f) ∧ (∀ x: X, a # (f x)) }.

Theorem freshness_theorem `{Nominal X} (f: Name →ₛ X): 
  ∀ a b, (∃ (c: Name), c ∉ support f ∧ c # (f c)) → 
  a # f → b # f → f a ≡ f b.
Proof. 
  intros ? ? [c []] ? ?. 
  rewrite <-(fresh_fixpoint c a f) at 1; auto; try (apply support_fresh; assumption).
  rewrite <-(fresh_fixpoint c b f) at 2; auto; try (apply support_fresh; assumption).
  unfold action, fun_supp_act; simpl; rewrite <-!perm_inv, !name_action_right.
  destruct (decide (c = a)), (decide (c = b)); subst; try rewrite perm_action_equal.
  - reflexivity.
  - rewrite fresh_fixpoint; [reflexivity | assumption | idtac].
    apply fresh_fun_supp; auto; apply name_neq_fresh_iff, not_eq_sym; assumption.
  - rewrite fresh_fixpoint; [reflexivity | assumption | idtac].
    apply fresh_fun_supp; auto; apply name_neq_fresh_iff, not_eq_sym; assumption.
  - rewrite !fresh_fixpoint; try reflexivity; try assumption;
      apply fresh_fun_supp; auto; apply name_neq_fresh_iff, not_eq_sym; assumption.
Qed. *)


(* all this lemmas can be rewritten using a much more general lemma *)

(* Lemma perm_distr_1 (a b w z: Name) (p: Perm):
  w ≠ a → w ≠ b → z ≠ a → z ≠ b →
  ⟨a,b⟩ + (⟨w, z⟩•p) ≡ (⟨w, z⟩•⟨a,b⟩) + (⟨w,z⟩•p).
Proof.
  intros; rewrite <-(fresh_fixpoint w z (⟨ a, b ⟩)) at 1; auto;
  apply support_fresh; set_solver.
Qed.

Lemma perm_distr_2 (a b w z: Name) (p: Perm):
  (⟨w,z⟩•⟨a,b⟩) + (⟨w,z⟩•p) ≡ ⟨w,z⟩•(⟨a,b⟩ + p).
Proof.
  unfold action, PermActionPerm; rewrite <-perm_inv, !grp_assoc.
  assert (H: ⟨w,z⟩+⟨a,b⟩+⟨w,z⟩+⟨w,z⟩+p+⟨w,z⟩ ≡ ⟨w,z⟩+⟨a,b⟩+(⟨w,z⟩+⟨w,z⟩)+p+⟨w,z⟩). {
    rewrite !grp_assoc; reflexivity.
  }
  rewrite H, perm_duplicate; clear H.
  assert (H: ⟨w,z⟩+⟨a,b⟩+ɛ+p+⟨w,z⟩ ≡ ⟨w,z⟩+⟨a,b⟩+(ɛ+(p+⟨w,z⟩))). {
    rewrite !grp_assoc; reflexivity.
  }
  rewrite H, grp_left_id, !grp_assoc; reflexivity.
Qed.

Lemma perm_distr_3 (a b w z: Name) (p: Perm):
  w ∉ perm_dom p → z ∉ perm_dom p → w ≠ a → z ≠ a →
  ⟨w,z⟩•⟨a,b⟩+p ≡ ⟨a,⟨w,z⟩•b⟩+p.
Proof.
  intros Pw Pz ? ?; rewrite perm_distr; do 2 unfold action at 1; unfold perm_action.
  assert (HH1: -⟨w,z⟩+(⟨a,b⟩+⟨w,z⟩)+(-⟨w,z⟩+(p+⟨w,z⟩)) ≡ (⟨a,⟨w,z⟩•b⟩+p)). {
    rewrite <-perm_inv, !grp_assoc.
    assert (HH2: ⟨w,z⟩+⟨a,b⟩+⟨w,z⟩+⟨w,z⟩+p+⟨w,z⟩ ≡ ⟨w,z⟩+⟨a,b⟩+p+⟨w,z⟩). {
      assert (HH3: ⟨w,z⟩+⟨a,b⟩+⟨w,z⟩+⟨w,z⟩+p+⟨w,z⟩ ≡ ⟨w,z⟩+⟨a,b⟩+(⟨w,z⟩+⟨w,z⟩)+p+⟨w,z⟩). {
      rewrite !grp_assoc; reflexivity.
      } rewrite HH3, perm_duplicate; clear HH3.
      assert (HH3: ⟨w,z⟩+⟨a,b⟩+ɛ+p+⟨w,z⟩ ≡ ⟨w,z⟩+⟨a,b⟩+(ɛ+(p+⟨w,z⟩))). {
        rewrite !grp_assoc; reflexivity.
      } rewrite HH3, grp_left_id, !grp_assoc; reflexivity.
    } rewrite HH2; clear HH2; pose proof (perm_notin_dom_comm w z p Pw Pz) as HH.
    assert (HH2: ⟨w,z⟩+⟨a,b⟩+p+⟨w,z⟩ ≡ ⟨w,z⟩+⟨a,b⟩+⟨w,z⟩+p). {
      assert (HH3: ⟨w,z⟩+⟨a,b⟩+p+⟨w,z⟩ ≡ ⟨w,z⟩+⟨a,b⟩+(p+⟨w,z⟩)). {
        rewrite !grp_assoc; reflexivity.
      } rewrite HH3, <-HH, grp_assoc; reflexivity.
    } rewrite HH2; clear HH2.
    pose proof (perm_comm_distr a b ⟨ w, z ⟩) as H2; rewrite perm_swap_neither in H2;
    try (apply not_eq_sym; auto).
    assert (HH2: ⟨w,z⟩+⟨a,b⟩+⟨w,z⟩+p ≡ ⟨w,z⟩+(⟨a,b⟩+⟨w,z⟩)+p). {
      rewrite !grp_assoc; reflexivity.
    } rewrite HH2, H2, !grp_assoc, perm_duplicate, grp_left_id; 
    unfold action; simpl; reflexivity.
  }
  assert (HH2: (-⟨w,z⟩+(⟨a,b⟩+⟨w,z⟩)+(-⟨w,z⟩+(p+⟨w,z⟩))) ≡ (⟨a,⟨w,z⟩•b⟩+p)). {
    rewrite HH1; reflexivity.
  } rewrite HH2; reflexivity.
Qed. *)

Tactic Notation "eabstract" tactic3(tac) :=
let G := match goal with |- ?G => G end in
let pf := constr:(ltac:(tac) : G) in
abstract exact_no_check pf.

(* Lemma perm_swap_subst_name a b c: 
  b ≠ c → subst_name c b a = perm_swap ⟨ a, b ⟩ c.
Proof.
  intros; unfold subst_name; simpl;
  destruct (_ =n _); repeat destruct (decide (_ = _)); subst; auto;
  try congruence.
Qed. *)

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

(* Lemma action_subst a b t: b ∉ atm1 t → (subst t b a) = ⟨a, b⟩ • t.
Proof.
  intros; induction t using term_ind_general.
  - unfold action; simpl; unfold action, name_action; rewrite perm_swap_subst_name;
    auto; set_solver.
  - simpl in *; rewrite action_app; f_equal; [apply IHt1 | apply IHt2]; set_solver.
  - simpl in *; rewrite action_lam; do 2 f_equal; [apply perm_swap_subst_name | apply IHt]; set_solver.
Qed. *)


Section InductionAlpha. (* COPELLO's *)

Definition αCompat (P: Term → Prop) : Prop := ∀ m n, aeqCof m n → P m → P n.

Lemma perm_ind:
  ∀ P: Term → Prop, αCompat P →
    (∀ t, P (Var t)) →
    (∀ m n, P m → P n → P (App m n)) →
    (∀ a m, (∀ p, P (p • m)) → P (Lam a m)) →
    ∀ t, P t.
Proof.
  intros P Compat Hvar Happ Hlam t.
  apply (Compat (ɛ • t) _ (gact_id t)). 
  apply (@Term_ind (fun t => ∀ p, P (p • t))).
    + intros; rewrite perm_var; apply Hvar.
    + intros; rewrite perm_app; apply Happ; auto.
    + intros; rewrite perm_lam; apply Hlam; intros.
      eapply (Compat ((p + p0) • t1)). 
      * rewrite gact_compat; reflexivity.
      * apply H.
Qed.

Lemma aeq_lam_swap_notin (a b: Name) (t: Term) : 
  b ∉ (fv (Lam a t)) → aeqCof (Lam a t) (Lam b (⟨a,b⟩•t)).
Proof.
  intros; simpl in *; apply not_elem_of_difference in H as [].
  - apply AeqAbsC with (L := fv t ∪ support b ∪ support a); intros; destruct (decide (a = b)); subst.
    + rewrite perm_swap_distr, perm_swap_left, term_action_equal; reflexivity.
    + rewrite perm_swap_distr, perm_swap_left, perm_swap_neither; [| set_solver | set_solver].
      apply term_perm_alpha. rewrite support_spec; set_solver.
  - apply elem_of_singleton in H; subst; rewrite term_action_equal; reflexivity.
Qed.

Lemma lam_rename:
  ∀ P: Term → Prop, αCompat P →
    ∀ L : NameSet,
      (∀ b m, b ∉ L → (∀ p, P (p • m)) → P (Lam b m)) →
      ∀ a m, (∀ p, P (p • m)) → P (Lam a m).
Proof.
  intros P Compat L HLam a m Hp. set (c := fresh (support (Lam a m) ∪ L)).
  apply (Compat (Lam c (⟨a,c⟩•m))).
  - symmetry. apply aeq_lam_swap_notin. subst c; unfold support, TermSupport; simpl.
    eapply not_elem_of_weaken; [eapply is_fresh | set_solver].
  - apply HLam.
    + subst c. eapply not_elem_of_weaken; [eapply is_fresh | set_solver].
    + intros; eapply (Compat ((⟨a,c⟩ + p) • m)).
      * rewrite gact_compat; reflexivity.
      * apply Hp.
Qed.

Definition alpha_ind (L : NameSet) :
  ∀ P: Term → Prop, αCompat P →
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
  - apply lam_rename with L; auto.
    intros b m HbL HP; apply HLam.
    + assumption.
    + apply (Compat (ɛ • m)); [apply gact_id | apply HP].
Qed.

End InductionAlpha.

Section RecursionAlpha.
  Context `{Nominal X} (L : NameSet).
  Context (fvar : Name →ₛ X) (fapp : (X * X) →ₛ X) (flam : [𝔸]X →ₛ X).
  Context (fvarL : f_supp fvar ⊆ L) (fappL : f_supp fapp ⊆ L) (flamL : f_supp flam ⊆ L).
  Context (fcb : ∃ a, a ∉ L ∧ ∀ x, a # flam [a]x).

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
    refine (λₛ⟦ L ∪ support Fm ∪ support Fn⟧ p, fapp (Fm p, Fn p)).
  Proof.
    - intros ? ? HH; rewrite HH; reflexivity.
    - intros w z [[]%not_elem_of_union]%not_elem_of_union [[]%not_elem_of_union]%not_elem_of_union p.
      rewrite <-(fresh_fixpoint w z Fm) at 1; try (apply support_fresh; set_solver);
      rewrite <-(fresh_fixpoint w z Fn) at 1; try (apply support_fresh; set_solver);
      rewrite <-2!fun_equivar, <-prod_act; rewrite perm_inv at 2; rewrite <-fsupp_action;
      rewrite fresh_fixpoint; try (apply support_fresh; set_solver); reflexivity.
  Defined.

  Local Lemma ft_flam (Fm: Perm →ₛ X) a p (Sp: NameSet): 
    ∃ c : Name, (c ∉ Sp) ∧ c # flam [c](Fm (⟨a,c⟩ + p)).
  Proof.
    destruct (exist_fresh (Sp ∪ support flam)) as [w Hw]; exists w; split.
    - set_solver.
    - destruct fcb as [d [? Hd]].
      specialize (Hd (⟨d,w⟩•(Fm (⟨a,w⟩ + p)))).
      apply ((fresh_equivariant ⟨d,w⟩ _ _)) in Hd; rewrite perm_swap_left in Hd.
      rewrite <-(fresh_fixpoint d w flam), fsupp_action, <-perm_inv, nabs_action, name_action_right;
      [apply Hd | |]; apply support_fresh; set_solver.
  Qed.

  Definition g_lam (a: Name) (m: Term) (Fm: Perm →ₛ X): Perm →ₛ X.
    refine (
      λₛ⟦ L ∪ support a ∪ support (Fm) ⟧ p,
        let h: Name →ₛ X := λₛ⟦support flam ∪ support a ∪ support m ∪ support (Fm) ∪ support p⟧ a', 
          (flam [a'](Fm (⟨a,a'⟩ + p))) in freshF h
    ).
    all: swap 1 2.
    - intros w z Hw Hz p; unfold freshF; cbn zeta.
      set (g := (λₛ⟦ _ ⟧ a' : Name, flam [a'](Fm (⟨ a, a' ⟩ + (⟨ w, z ⟩ • p))))).
      set (h := (λₛ⟦ _ ⟧ a' : Name, flam [a'](Fm (⟨ a, a' ⟩ + p)))).
      destruct (exist_fresh (support flam ∪ support a ∪ support m ∪ support (Fm) ∪ support w ∪ support z ∪ support (⟨ w, z ⟩ • p) ∪ support p)) as [b Hb].
      rewrite (freshness_theorem2 g (fresh (support g)) b), (freshness_theorem2 h (fresh (support h)) b);
      try (apply fresh_support_fresh); try (apply support_fresh; subst h g; unfold support at 1; simpl; split_union; repeat (apply not_elem_of_union; split; try eauto)).
      all: swap 1 2. all: swap 2 3; try (subst; simpl; apply ft_flam).
      + subst g h; simpl.
        assert (HH: flam [b](Fm (⟨a,b⟩+(⟨w,z⟩•p))) ≡ flam [b]((⟨w,z⟩•(Fm)) (⟨w,z⟩•⟨a,b⟩+p))). {
        apply fsupp_equiv, nabs_inv;
        rewrite perm_distr_1, perm_distr,<-(fresh_fixpoint w z (Fm)) at 1;
        try reflexivity; try (apply support_fresh); set_solver.
        } rewrite HH; clear HH.
        rewrite <-(fresh_fixpoint w z b) at 1; try (apply support_fresh; set_solver).
        assert (HH: flam [⟨w,z⟩•b]((⟨w,z⟩•(Fm)) (⟨w,z⟩•⟨a,b⟩+p)) ≡ flam ([⟨w,z⟩•b](⟨w,z⟩•(Fm (⟨a,b⟩+p))))). {
        apply fsupp_equiv, nabs_inv; rewrite fun_equivar; reflexivity.
        } rewrite HH; clear HH.
        rewrite <-nabs_action,<-fsupp_action, fresh_fixpoint; try (apply support_fresh; set_solver);
        reflexivity.
      - intros x y Hxy; unfold freshF; cbn zeta; set (a' := fresh _); set (b' := fresh _);
        set (g := (λₛ⟦ _ ⟧ _ : Name, flam [_](Fm (⟨ a, _ ⟩ + x))));
        set (h := (λₛ⟦ _ ⟧ _' : Name, flam [_](Fm (⟨ a, _ ⟩ + y))));
        destruct (exist_fresh (support flam ∪ support a ∪ support m ∪ support (Fm) ∪ support x ∪ support y ∪ support a' ∪ support b')) as [c Hc];
        rewrite (freshness_theorem2 g a' c), (freshness_theorem2 h b' c);
        try (apply fresh_support_fresh); try (apply support_fresh; subst h g; unfold support at 1; simpl; split_union; repeat (apply not_elem_of_union; split; try eauto));
        try (subst; simpl; apply ft_flam);
        simpl; apply fsupp_equiv, nabs_inv, fsupp_equiv, grp_op_proper; auto.
  Unshelve.
    eabstract(
      intros w z Hw Hz b;
      rewrite <-(fresh_fixpoint w z flam) at 2; try (apply support_fresh; set_solver);
      rewrite fsupp_action, <-perm_inv, nabs_action; apply gact_proper, fsupp_equiv; auto;
      rewrite (fun_equivar (⟨w,z⟩) (Fm)), (fresh_fixpoint w z (Fm)); try (apply support_fresh; set_solver);
      rewrite perm_distr_3; set_solver
    ).
  Defined.

  Fixpoint perm_alpha_rec (t: Term) : (Perm →ₛ X) :=
    match t with
    | Var a => g_var a
    | App m n => g_app (perm_alpha_rec m) (perm_alpha_rec n)
    | Lam a m => g_lam a m (perm_alpha_rec m)
    end.

  Functional Scheme perm_alpha_rec_ind := Induction for perm_alpha_rec Sort Prop.
  
  Lemma perm_alpha_rec_app (m n: Term):
    perm_alpha_rec (App m n) = g_app (perm_alpha_rec m) (perm_alpha_rec n).
  Proof. simpl; reflexivity. Qed.

  Lemma perm_alpha_rec_lam a (m: Term):
    perm_alpha_rec (Lam a m) = g_lam a m (perm_alpha_rec m).
  Proof. simpl; reflexivity. Qed.

  Lemma alpha_rec_perm (t: Term):
    ∀ (p q: Perm), perm_alpha_rec t (q + p) ≡ perm_alpha_rec (q • t) p.
  Proof. 
    induction t; intros.
    - simpl; rewrite gact_compat; reflexivity.
  Admitted.

  (* Lemma support_perm_alpha_rec t: 
    support (perm_alpha_rec t) ⊆ (L ∪ support t).
  Proof.
    induction t; unfold support in *; simpl. 
    - unfold support,name_support; simpl; set_solver.
    - unfold support,fun_supp_support in *; simpl in *.
      repeat (apply union_subseteq; split).
      + apply union_subseteq_l.
      + eapply union_subseteq_l' in IHt1. admit.
      + eapply union_subseteq_l' in IHt2. admit. 
    - admit.
  Admitted. *)

(* perhaps can be made simpler *)
  Theorem perm_alpha_rec_respectfull (m n : Term) :
    aeqCof m n → perm_alpha_rec m ≡ perm_alpha_rec n.
  Proof.
    induction 1.
    - simpl; unfold g_var; reflexivity.
    - simpl; unfold g_app; unfold equiv, fun_supp_equiv; intro p; simpl.
      rewrite IHaeqCof1, IHaeqCof2; reflexivity.
    - simpl; unfold g_lam, equiv, fun_supp_equiv; intros p; simpl.
      set (s1 := support flam ∪ support a ∪ support m ∪ support (perm_alpha_rec m) ∪ support p);
      set (s2 := support flam ∪ support b ∪ support n ∪ support (perm_alpha_rec n) ∪ support p).
      set (h1 := (λₛ⟦ s1 ⟧ a' : Name, flam [a'](perm_alpha_rec m (⟨ a, a' ⟩ + p))));
      set (h2 := (λₛ⟦ s2 ⟧ a' : Name, flam [a'](perm_alpha_rec n (⟨ b, a' ⟩ + p)))).
      assert (HH1: flam [fresh (support h1)](perm_alpha_rec m (⟨ a, fresh (support h1) ⟩ + p)) = h1 (fresh (support h1))).
      { subst h1 s1; reflexivity. }
      assert (HH2: flam [fresh (support h2)](perm_alpha_rec n (⟨ b, fresh (support h2) ⟩ + p)) = h2 (fresh (support h2))).
      { subst h2 s2; reflexivity. }
      rewrite HH1, HH2; clear HH1 HH2.
      destruct (exist_fresh (L0 ∪ support h2 ∪ support h1)) as [w Hw].
      (* destruct (exist_fresh (support a ∪ support b ∪ atms m ∪ atms n ∪ support h2 ∪ support h1 ∪ support flam ∪ L ∪ L0)) as [w Hw]. *)
      rewrite (freshness_theorem2 h1 (fresh (support h1)) w), (freshness_theorem2 h2 (fresh (support h2)) w).
      + subst h1 h2; simpl; apply fsupp_equiv; rewrite !alpha_rec_perm.
        apply name_abstraction_inv; left; split; auto.
        rewrite H2. reflexivity. apply not_elem_of_union in Hw as [[]%not_elem_of_union]. assumption.
      + apply ft_flam.
      + apply fresh_support_fresh.
      + apply support_fresh. apply not_elem_of_union in Hw as [[]%not_elem_of_union]. assumption.
      + apply ft_flam.
      + apply fresh_support_fresh.
      + apply support_fresh. apply not_elem_of_union in Hw as [[]%not_elem_of_union]. assumption.
  Qed.

  Instance: Proper (aeqCof ==> equiv) (perm_alpha_rec).
  Proof. repeat intro; apply perm_alpha_rec_respectfull; assumption. Qed.

  Definition alpha_rec (t: Term) := perm_alpha_rec t ɛ.

  Lemma alpha_rec_respectfull m n : 
    aeqCof m n → alpha_rec m ≡ alpha_rec n.
  Proof. intros; unfold alpha_rec; apply perm_alpha_rec_respectfull; assumption. Qed.

  Lemma alpha_rec_var a : 
    alpha_rec (Var a) = fvar a.
  Proof. unfold alpha_rec; simpl; rewrite gact_id; auto. Qed.

  Instance: Proper (aeqCof ==> equiv) (alpha_rec).
  Proof. repeat intro; apply alpha_rec_respectfull; assumption. Qed.
  
  Lemma alpha_rec_app (m n: Term):
    alpha_rec (App m n) = fapp (alpha_rec m, alpha_rec n).
  Proof. unfold alpha_rec; simpl; reflexivity. Qed.

  Lemma union_empty (A : NameSet) : A ≡ A ∪ ∅.
  Proof. set_solver. Qed.

  Lemma alpha_rec_lam a m:
    let h := fresh (support flam ∪ support a ∪ support m ∪ support (perm_alpha_rec m)) in
    alpha_rec (Lam a m) ≡ flam [h](alpha_rec (⟨a,h⟩•m)).
  Proof.
    intros; unfold alpha_rec; simpl; unfold support at 1; simpl.
    set (b := fresh _).
    assert (HH: h = b). { subst h b; unfold support; simpl; apply fresh_proper, union_empty. }
    apply fsupp_equiv, name_abstraction_inv; left; split.
    - auto. 
    - rewrite HH, alpha_rec_perm; reflexivity.
  Qed.

  Theorem alpha_rec_support (a b : Name) (t : Term) :
    a ∉ L → b ∉ L → ⟨a,b⟩•(alpha_rec (⟨a,b⟩•t)) ≡ alpha_rec t.
  Proof.
    intros; generalize t; apply (alpha_ind L).
    - repeat intro.
      pose proof (term_perm_alpha ⟨a,b⟩ _ _ H3).
      pose proof (alpha_rec_respectfull _ _ H3).
      pose proof (alpha_rec_respectfull _ _ H5).
      assert (HH: ⟨ a, b ⟩ •(alpha_rec (⟨ a, b ⟩ • m)) ≡ ⟨ a, b ⟩ •(alpha_rec (⟨ a, b ⟩ • n))).
      { apply perm_inj; assumption. }
      symmetry in HH; etransitivity.
      + eauto.
      + etransitivity.
        * eauto.
        * assumption.
    - intros; rewrite alpha_rec_var; apply support_spec.


End RecursionAlpha.

  (* Definition alpha_rec1 (p : Perm) : Term →ₛ X.
    refine (λₛ⟦ L ⟧ t, perm_alpha_rec t p).
  Proof.
    - admit.
    - intros; generalize dependent p; induction x as [| | c t].
      + admit.
      + admit.
      + intros p. destruct (decide (a = b)); subst. admit.
        destruct (decide (a = c)), (decide (b = c)); subst.
        * rewrite !perm_action_equal; reflexivity.
        * 




        pose proof (f_supp_spec _ _ (g_lam c t (perm_alpha_rec t))).
        rewrite <-H3.
      rewrite perm_lam. simpl.
        set (s1 := support flam ∪ support (⟨ a, b ⟩ • c) ∪ support (⟨ a, b ⟩ • t) ∪ support (perm_alpha_rec (⟨ a, b ⟩ • t)) ∪ support p).
        set (s2 := support flam ∪ support c ∪ support t ∪ support (perm_alpha_rec t) ∪ support p).
        set (h1 := λₛ⟦ s1 ⟧ a' : Name, flam [a'](perm_alpha_rec (⟨ a, b ⟩ • t) (⟨ ⟨ a, b ⟩ • c, a' ⟩ + p))).
        set (h2 := λₛ⟦ s2 ⟧ a' : Name, flam [a'](perm_alpha_rec t (⟨ c, a' ⟩ + p))).
        assert (HH1: flam [fresh (support h1)](perm_alpha_rec (⟨ a, b ⟩ • t) (⟨ ⟨ a, b ⟩ • c, fresh (support h1) ⟩ + p)) = h1 (fresh (support h1))).
        { subst s1 h1; reflexivity. }
        assert (HH2: flam [fresh (support h2)](perm_alpha_rec t (⟨ c, fresh (support h2) ⟩ + p)) = h2 (fresh (support h2))).
        { subst s2 h2; reflexivity. }
        rewrite HH1,HH2; clear HH1 HH2.
        destruct (exist_fresh (L ∪ support h1 ∪ support h2 ∪ support a ∪ support b)) as [z Hz].
        rewrite (freshness_theorem2 h1 (fresh (support h1)) z), (freshness_theorem2 h2 (fresh (support h2)) z).
        * subst h1 h2; simpl. rewrite fun_equivar, fresh_fixpoint.
          -- rewrite nabs_action, fresh_fixpoint.
            ++ apply fsupp_equiv,nabs_inv. destruct (decide (a = b)); subst.
              ** admit. (* reflexivity *)
              ** destruct (decide (a = c)), (decide (b = c)); subst.
                --- admit.
                --- rewrite (name_action_left c b). rewrite IHt.
                    
                
                rewrite alpha_rec_perm.
                    
            
            
            
             rewrite IHt, fresh_fixpoint. reflexivity.
            
            
             rewrite fun_equivar, fresh_fixpoint.
              ** admit.
              ** apply support_fresh.
               rewrite alpha_rec_perm.
            rewrite (alpha_rec_perm t ⟨w,z⟩).
            ++ apply not_elem_of_union in Hz as [[]%not_elem_of_union]. unfold support,name_support in *.
               apply name_neq_fresh_iff. set_solver.
            ++ apply not_elem_of_union in Hz as [[]%not_elem_of_union]. unfold support,name_support in *.
               apply name_neq_fresh_iff. set_solver.
          -- eapply support_fresh,not_elem_of_weaken; eauto.
          -- eapply support_fresh,not_elem_of_weaken; eauto.
        * apply ft_flam.
        * apply fresh_support_fresh.
        * apply support_fresh. apply not_elem_of_union in Hz as [[]%not_elem_of_union]. assumption.
  Admitted. *)

  (* Definition alpha_rec : Term →ₛ X.
    refine (λₛ⟦ L ⟧ t, perm_alpha_rec t ɛ).
  Proof.
    - repeat intro; apply perm_alpha_rec_respectfull; assumption.
    - intros a b ? ? t. 
      functional induction (perm_alpha_rec t) using perm_alpha_rec_ind.
      + simpl. rewrite fun_equivar,fresh_fixpoint.
        * rewrite !gact_compat,grp_left_id,perm_duplicate; reflexivity.
        * apply support_fresh; set_solver.
        * apply support_fresh; set_solver.
      + rewrite perm_app, perm_alpha_rec_app; simpl; rewrite fun_equivar, fresh_fixpoint.
        * rewrite <-IHf; rewrite <-IHf0; reflexivity.
        * eapply support_fresh,not_elem_of_weaken; eauto.
        * eapply support_fresh,not_elem_of_weaken; eauto.
      + rewrite perm_lam, perm_alpha_rec_lam; rewrite fun_equivar, fresh_fixpoint.
        * simpl. set (s := support _). set (s' := support _). 








    
     generalize dependent a; generalize dependent b; induction t as [| | w t].
      + intros; simpl; rewrite fun_equivar,fresh_fixpoint.
        * rewrite !gact_compat,grp_left_id,perm_duplicate; reflexivity.
        * apply support_fresh; set_solver.
        * apply support_fresh; set_solver.
      + intros; rewrite perm_app, perm_alpha_rec_app; simpl; rewrite fun_equivar, fresh_fixpoint.
        * rewrite <-(IHt1 b H2 a H1), <-(IHt2 b H2 a H1). reflexivity.
        * eapply support_fresh,not_elem_of_weaken; eauto.
        * eapply support_fresh,not_elem_of_weaken; eauto.
      + intros b ? a ?. (* destruct (decide (a = b)); subst.
        * rewrite perm_action_equal; apply perm_alpha_rec_respectfull; rewrite perm_action_equal; reflexivity.
        * *)
           
      
      
      
       rewrite perm_lam; simpl.
        set (s1 := support flam ∪ support (⟨ a, b ⟩ • w) ∪ support (⟨ a, b ⟩ • t) ∪ support (perm_alpha_rec (⟨ a, b ⟩ • t)) ∪ support ɛ);
        set (s2 := support flam ∪ support w ∪ support t ∪ support (perm_alpha_rec t) ∪ support ɛ).
        set (h1 := λₛ⟦ s1 ⟧ a' : Name, flam [a'](perm_alpha_rec (⟨ a, b ⟩ • t) (⟨ ⟨ a, b ⟩ • w, a' ⟩ + ɛ)));
        set (h2 := λₛ⟦ s2 ⟧ a' : Name, flam [a'](perm_alpha_rec t (⟨ w, a' ⟩ + ɛ))).
        assert (HH1: flam [fresh (support h1)](perm_alpha_rec (⟨ a, b ⟩ • t) (⟨ ⟨ a, b ⟩ • w, fresh (support h1) ⟩ + ɛ)) = h1 (fresh (support h1))).
        { subst s1 h1; reflexivity. }
        assert (HH2: flam [fresh (support h2)](perm_alpha_rec t (⟨ w, fresh (support h2) ⟩ + ɛ)) = h2 (fresh (support h2))).
        { subst s2 h2; reflexivity. }
        rewrite HH1,HH2; clear HH1 HH2.
        destruct (exist_fresh (L ∪ support h1 ∪ support h2 ∪ support a ∪ support b ∪ support w)) as [z Hz].
        rewrite (freshness_theorem2 h1 (fresh (support h1)) z), (freshness_theorem2 h2 (fresh (support h2)) z).
        * subst h1 h2; simpl. rewrite fun_equivar, fresh_fixpoint.
          -- rewrite nabs_action, fresh_fixpoint.
            ++ apply fsupp_equiv,nabs_inv. rewrite! alpha_rec_perm.
               destruct (decide (a = w)), (decide (b = w)); subst.
               ** admit.
               **   
              ** admit.  
              ** apply support_fresh.
               assert (HHg: ∀ (g : Perm), g + ɛ ≡ ɛ + g). { admit. }
               rewrite alpha_rec_perm.
            rewrite (alpha_rec_perm t ⟨w,z⟩).
            ++ apply not_elem_of_union in Hz as [[]%not_elem_of_union]. unfold support,name_support in *.
               apply name_neq_fresh_iff. set_solver.
            ++ apply not_elem_of_union in Hz as [[]%not_elem_of_union]. unfold support,name_support in *.
               apply name_neq_fresh_iff. set_solver.
          -- eapply support_fresh,not_elem_of_weaken; eauto.
          -- eapply support_fresh,not_elem_of_weaken; eauto.
        * apply ft_flam.
        * apply fresh_support_fresh.
        * apply support_fresh. apply not_elem_of_union in Hz as [[]%not_elem_of_union]. assumption.

        set (c := fresh _); set (d := fresh _).
        assert (HH1: perm_alpha_rec (⟨a,b⟩•t) (⟨⟨a,b⟩•w,c⟩ + ɛ) ≡ perm_alpha_rec (⟨⟨a,b⟩•w,c⟩•(⟨a,b⟩•t)) ɛ). { apply alpha_rec_perm. }
        assert (HH2: perm_alpha_rec t (⟨w,d⟩ + ɛ) ≡ perm_alpha_rec (⟨w,d⟩•t) ɛ). { apply alpha_rec_perm. }
        
        
        
        
        
        destruct (decide (a = b)); subst.
        * rewrite !perm_action_equal. apply fsupp_equiv. rewrite !perm_action_equal.
          apply name_abstraction_inv; left; 
          assert (Heq: c = d). {
            subst c d; apply nameset_fresh_respect;
             unfold support,TermSupport; simpl. rewrite !perm_action_equal,!lala. reflexivity.
          } 
          split. assumption. rewrite Heq; reflexivity.
        * rewrite fun_equivar,fresh_fixpoint.
          -- apply fsupp_equiv. rewrite nabs_action.
          -- eapply support_fresh,not_elem_of_weaken; eauto.
          -- eapply support_fresh,not_elem_of_weaken; eauto. *)

  

  (* Lemma alpha_rec_lam1 a m:
    let h := fresh (support flam ∪ support a ∪ support m ∪ support (perm_alpha_rec m)) in
    alpha_rec (Lam (a,m)) ≡ flam [h](alpha_rec (⟨a,h⟩•m)).
  Proof.
    intros; unfold alpha_rec; simpl; unfold support at 1; simpl.
    set (b := fresh _).
    assert (HH: h = b). { subst h b; unfold support; simpl; apply fresh_proper; set_solver. } 
    apply fsupp_equiv, name_abstraction_inv; left; split.
    - auto. 
    - rewrite HH, alpha_rec_perm; reflexivity.
  Qed. *)

  (* Lemma g_var_support a : support (g_var a) ⊆ (support fvar ∪ support a).
  Proof. unfold support at 1. simpl. *)

  (* Lemma support_alpha m: 
    support (perm_alpha_rec m) ⊆ support fvar ∪ support fapp ∪ support flam ∪ support m.
  Proof. 
    induction m; unfold support at 1; simpl.
    - unfold support,name_support; simpl. admit.
    - admit.
    - unfold support at 6; simpl.

      + admit.
      + set_solvre.
     set_solver. Qed. *)

  (* Lemma alpha_rec_lam_exists_abs m:
    ∃ L: NameSet, ∀ a, a ∉ L → alpha_rec (Lam a m) ≡ flam [a](alpha_rec m).
  Proof. Admitted. *)
    (* exists (support flam ∪ support m ∪ support (perm_alpha_rec m)); intros.
    intros; unfold alpha_rec; simpl; unfold support at 1; simpl.
    set (w := fresh _).
    apply fsupp_equiv, name_abstraction_inv; right; split.
    - apply alpha_class_inv; right; split.
      + apply not_eq_sym; apply name_neq_fresh_iff, support_fresh; subst w.
        eapply not_elem_of_weaken.
        * eapply is_fresh.
        * set_solver.
      + apply fresh_fun_supp; apply support_fresh; subst w; eapply not_elem_of_weaken;
        try eapply is_fresh; set_solver.
    - rewrite alpha_rec_perm, fun_equivar, (fresh_fixpoint w a).
      + rewrite (fresh_fixpoint a w).
        * apply fsupp_equiv; unfold action, perm_action.
          rewrite grp_left_id, grp_left_inv; reflexivity.
        * apply support_fresh; set_solver.
        * apply support_fresh. subst w;
          eapply not_elem_of_weaken.
          -- eapply is_fresh.
          -- set_solver.
      + apply support_fresh; subst w; eapply not_elem_of_weaken.
        * eapply is_fresh.
        * set_solver.
      + apply support_fresh; set_solver.
  Qed. *)

  (* Lemma alpha_rec_lam_exists m:
    ∀ a, a ∉ (support fvar ∪ support fapp ∪ support flam ∪ atm1 m) → 
    alpha_rec (Lam [a]m) ≡ flam [a](alpha_rec m).
  Proof.
  intros; unfold alpha_rec; simpl; unfold support at 1; simpl; set (w := fresh _).
  apply fsupp_equiv, name_abstraction_inv; right; split.
  - apply alpha_class_inv; right; split.
    + apply not_eq_sym; apply name_neq_fresh_iff, support_fresh; subst w.
      eapply not_elem_of_weaken.
      * eapply is_fresh.
      * set_solver.
    + apply fresh_fun_supp; apply support_fresh; subst w; eapply not_elem_of_weaken;
      try eapply is_fresh; set_solver.
  - rewrite alpha_rec_perm, fun_equivar, (fresh_fixpoint w a).
    + rewrite <-alpha_rec_perm. unfold action, perm_action; rewrite (fresh_fixpoint a w).
      * apply fsupp_equiv; unfold action, perm_action.
        rewrite grp_left_id, grp_left_inv; reflexivity.
      * apply support_fresh. set_solver.
      * apply support_fresh; subst w.
        eapply not_elem_of_weaken.
        -- eapply is_fresh.
        -- set_solver.
    + apply support_fresh; subst w; eapply not_elem_of_weaken.
      * eapply is_fresh.
      * set_solver.
    + eapply support_fresh, not_elem_of_weaken.
      * eauto.
      * apply support_alpha.
  Qed. *)

(* Lemma perm_empty p : p • ɛ ≡@{Perm} ɛ.
Proof. unfold action, perm_action; simpl. Admitted. *)

(* Definition perm_alpha_rec1 : Term →ₛ X.
  refine (
    λₛ⟦ L ⟧ t, alpha_rec t
  ).
Proof.
  - unfold alpha_rec; repeat intro; rewrite H1; reflexivity.
  - intros a b Sa Sb x; induction x using term_ind_general.
    + unfold alpha_rec; rewrite action_var; simpl.
      rewrite fun_equivar, fresh_fixpoint; try (apply support_fresh; set_solver).
      rewrite !gact_compat, !grp_assoc, grp_right_id, perm_duplicate; reflexivity.
    + rewrite action_app, !alpha_rec_app, fun_equivar, fresh_fixpoint; try (apply support_fresh; set_solver).
      apply fsupp_equiv; unfold equiv, prod_equiv, prod_relation; simpl; split; auto.
    + unfold alpha_rec in *; rewrite <-alpha_rec_perm, grp_right_id. 
      simpl; set (w := fresh _); set (w' := fresh _).
      rewrite perm_alpha_rec_lam.
    
    unfold alpha_rec. destruct (decide (a = a0)), (decide (b = a0)); subst.
      * unfold alpha_rec; rewrite !perm_action_equal; reflexivity.
      * rewrite action_lam, name_action_left.
        assert (HH: Lam (b,⟨a0,b⟩•x) ≡ Lam (a0,x)). { admit. }
        etransitivity; [| apply alpha_rec_respectfull; apply HH].
        rewrite alpha_rec_lam1; set (w := fresh _).
        rewrite fun_equivar, fresh_fixpoint; try (apply support_fresh; set_solver).
        rewrite nabs_action; apply fsupp_equiv. *)
      (* * admit.
      * rewrite action_lam. 

    rewrite action_lam, !alpha_rec_lam1; set (w := fresh _); set (w' := fresh _).
      rewrite fun_equivar, fresh_fixpoint; try (apply support_fresh; set_solver).
      rewrite nabs_action; apply fsupp_equiv.
      apply name_abstraction_inv; right; split.
      * admit.
      * unfold alpha_rec; rewrite !gact_compat, perm_comm_distr.
        destruct (decide (a = a0)), (decide (b = a0)); subst.
        -- rewrite perm_action_equal.

    unfold equiv, fun_supp_equiv; intros p; rewrite action_lam; simpl.
    set (w := fresh _); set (w' := fresh _).
    rewrite fun_equivar, fresh_fixpoint; try (apply support_fresh; set_solver).
    unfold action at 1; unfold name_abstraction_action; simpl.
    apply fsupp_equiv, name_abstraction_inv; right; split.
    + apply alpha_class_inv; left; subst w w'; unfold support at 1; unfold support at 6; unfold fun_supp_support; simpl. *)



Section TermLength.

  From Nominal Require Import Instances.Nat.
  
  Fixpoint term_length (t: Term): nat :=
    match t with
    | Var a => 1
    | App m n => (term_length m) + (term_length n)
    | Lam a m => 1 + (term_length m)
    end.

  Definition length_fvar: Name →ₛ nat.
  Proof. refine (λₛ⟦∅⟧ n, 1); intros; apply perm_nat. Defined.

  Definition length_fapp: (nat * nat) →ₛ nat.
  Proof. 
    refine (λₛ⟦∅⟧ mn, ((fst mn) + (snd mn))%nat).
    - intros [] [] [H1 H2]; simpl in *; rewrite H1,H2; reflexivity.
    - intros ? ? ? ? []; simpl; rewrite !perm_nat; reflexivity.
  Defined.

  (* Instance: Reflexive (≈α). Proof. Admitted. *)
  Instance: Proper (equiv ==> (≈α)) abs.
  Proof. repeat intro; unfold equiv,name_abstraction_equiv in *;
    destruct x as [[x n]]; destruct y as [[y m]]; assumption.
  Qed.

  Instance:  Proper (equiv ==> equiv) snd.
  Proof. intros [] [] [? []]; simpl; rewrite !perm_nat in *; assumption. Qed.

  Definition length_flam: [𝔸]nat →ₛ nat.
  Proof.
    refine (λₛ⟦∅⟧ (an: [𝔸]nat), (1 + (snd an))%nat).
    - repeat intro. rewrite H; reflexivity.
    - intros; rewrite !perm_nat; unfold action, name_abstraction_action; simpl; rewrite !perm_nat;
      reflexivity.
  Defined.

  Lemma name_fresh_nat (a: Name) (n: nat): a # n. Proof. Admitted.

  Lemma length_flam_fcb: FCB length_flam.
  Proof.
    unfold FCB; eexists; split.
    - unfold support; simpl; apply not_elem_of_empty.
    - intros; apply name_fresh_nat.
  Unshelve.
    (* we can use any name. Pick some default *)
    exact Atom.default.
  Qed.

  Lemma term_lenght_respectfull: ∀ m n, m ≡ n → term_length m = term_length n.
  Proof. Admitted. 

  Lemma equal a b m: alpha_rec length_fvar length_fapp length_flam (lamFCB := length_flam_fcb) (⟨a,b⟩•m) = alpha_rec length_fvar length_fapp length_flam (lamFCB := length_flam_fcb) m.
  Proof. Admitted.

  Lemma length_equal:
    ∀ t, term_length t = alpha_rec length_fvar length_fapp length_flam (lamFCB := length_flam_fcb) t.
  Proof.
    apply alpha_ind.
    - repeat intro; inversion H; subst;
      erewrite alpha_rec_respectfull, term_lenght_respectfull; eauto; symmetry.
      + assumption.
      + econstructor; eassumption.
    - intros; rewrite alpha_rec_var; simpl; reflexivity.
    - intros ? ? A B; rewrite alpha_rec_app; simpl in *; rewrite A, B; reflexivity.
    - pose proof (alpha_rec_lam_exists_abs length_fvar length_fapp length_flam (lamFCB := length_flam_fcb)).
    exists ∅; intros. simpl.
      pose proof alpha_rec_lam_exists_abs.

      pose proof (alpha_rec_lam length_fvar length_fapp length_flam (lamFCB := length_flam_fcb) a m).
      simpl in *. set (c := fresh _) in *.
      rewrite H1. f_equal.
    rewrite alpha_rec_lam.

End TermLength.