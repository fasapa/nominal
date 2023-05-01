From Nominal Require Import Nominal Fresh Alpha NameAbstraction.
From Nominal Require Import Instances.Name.

Require Import FunInd.

Inductive Term: Type :=
| Var: Name → Term
| App: Term → Term → Term
| Lam: (Name * Term) → Term.

Definition term_rect_general := fun (P : Term → Type)
  (fvar : ∀ a : Name, P (Var a))
  (fapp : ∀ t1: Term, P t1 → ∀ t2: Term, P t2 → P (App t1 t2))
  (flam : ∀ a : Name, ∀ t: Term, P t → P (Lam (a,t))) =>
  fix F (t: Term) : P t :=
    match t as t' return (P t') with
    | Var a => fvar a
    | App t1 t2 => fapp t1 (F t1) t2 (F t2)
    | Lam (a, t) => flam a t (F t)
    end.

Definition term_rec_general (P : Term → Set) := term_rect_general P.
Definition term_ind_general (P : Term → Prop) := term_rect_general P.

Fixpoint atm (t: Term) : NameSet.
Proof.
  apply term_rec_general.
  - exact (λ a, {[ a ]}).
  - exact (λ _ fm _ fn, fm ∪ fn).
  - exact (λ a _ fm, {[ a ]} ∪ fm).
  - exact t.
Defined.

Fixpoint atm1 (t: Term) : NameSet :=
  match t with
  | Var a => {[ a ]}
  | App t1 t2 => (atm1 t1) ∪ (atm1 t2)
  | Lam (a,t) => {[ a ]} ∪ (atm1 t)
  end.

Infix "=n" := Atom.dec (at level 90, no associativity).

Definition subst_name (a b c: Name): Name :=
  if a =n c then b else a.

Fixpoint subst (t: Term) (a' a: Name) : Term :=
  match t with
  | Var c => Var (subst_name c a' a)
  | App t1 t2 => App (subst t1 a' a) (subst t2 a' a)
  | Lam (c,t) => Lam ((subst_name c a' a), (subst t a' a))
  end.

Lemma subst_notin_atm t a b: b ∉ atm1 t → subst t a b = t.
Proof. induction t; intros.
  - simpl in *; unfold subst_name. admit.
  - admit.
  - admit.
Admitted.   

Inductive aeq: Term → Term → Prop :=
| AeqVar: ∀ a, aeq (Var a) (Var a)
| AeqApp: ∀ m n m' n', aeq m m' → aeq n n' → aeq (App m n) (App m' n')
| AeqAbs: ∀ (a b: Name) (m n: Term), 
    (∀ c, (c <> a ∧ c <> b) → (c ∉ atm1 m ∧ c ∉ atm1 n) → aeq (subst m c a) (subst n c b)) → 
    aeq (Lam (a,m)) (Lam (b,n)).

(* Necessario alguma relacao proper sobre os argumentos de aeq para
  facilitar reescrita *)

Lemma subst_equal: ∀ m a, (subst m a a) = m.
Proof. 
  induction m using term_ind_general; intros; simpl. 
  - unfold subst_name; destruct (_ =n _); subst; constructor.
  - rewrite IHm1, IHm2; reflexivity.
  - unfold subst_name; destruct (_ =n _); subst.
    + rewrite IHm; reflexivity.
    + rewrite IHm; reflexivity.
Qed.     

Lemma aeq_subst: ∀ m n a c, 
  c ≠ a → c ∉ atm1 m → c ∉ atm1 n →
  aeq m n → aeq (subst m c a) (subst n c a).
Proof. intros; induction H. Admitted.

(* #[export] Instance subst_proper: Proper (aeq ==> eq ==> eq ==> aeq) subst.
Proof. repeat intro; subst; apply aeq_subst; auto. Qed. *)

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

#[export] Instance: Equiv Term := aeq.

Fixpoint taction (p: Perm) (t: Term): Term :=
  match t with
  | Var a => Var (p • a)
  | App m n => App (taction p m) (taction p n)
  | Lam (a,m) => Lam ((p • a), (taction p m))
  end.

#[export] Instance: PermAction Term := taction.

Fixpoint fv (t: Term): NameSet :=
  match t with
  | Var a => {[ a ]}
  | App m n => (fv m) ∪ (fv n)
  | Lam (a,m) => (fv m) ∖ {[ a ]}
  end.

#[export] Instance: Support Term := fv.

#[export] Instance: PermT Term.
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
Admitted.

#[export] Instance: Nominal Term.
Proof.
    split.
    - typeclasses eauto.
    - intros t a b Sa Sb;
      unfold action, PermAction_instance_0, support, Support_instance_0,
                equiv, Equiv_instance_1 in *.
      induction t using term_ind_general; simpl in *.
      + rewrite support_spec; auto; reflexivity.
      + constructor; [apply IHt1 | apply IHt2]; set_solver.
      + apply not_elem_of_difference in Sa, Sb; destruct Sa, Sb.
        * econstructor; admit. (* a ∉ fv t ∧ b ∉ fv t*)
        * econstructor; admit. (* a ∉ fv t ∧ b = a0 *)
        * econstructor; admit. (* a = a0 ∧ b ∉ fv t*)
        * econstructor; admit. (* a = a0 ∧ b = a0 *)
Admitted.

From Nominal Require Import Instances.SupportedFunctions
  Instances.Name Instances.Prod Instances.Perm.

Definition FCB `{Nominal X, Nominal Y} (f: X →ₛ Y) :=
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
Qed.

Lemma perm_distr_1 (a b w z: Name) (p: Perm):
  w ≠ a → w ≠ b → z ≠ a → z ≠ b →
  ⟨a,b⟩ + (⟨w, z⟩•p) ≡ (⟨w, z⟩•⟨a,b⟩) + (⟨w,z⟩•p).
Proof.
  intros; rewrite <-(fresh_fixpoint w z (⟨ a, b ⟩)) at 1; auto;
  apply support_fresh; set_solver.
Qed.

Lemma perm_distr_2 (a b w z: Name) (p: Perm):
  (⟨w,z⟩•⟨a,b⟩) + (⟨w,z⟩•p) ≡ ⟨w,z⟩•(⟨a,b⟩ + p).
Proof.
  unfold action, perm_action; rewrite <-perm_inv, !grp_assoc.
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
Qed.

Tactic Notation "eabstract" tactic3(tac) :=
let G := match goal with |- ?G => G end in
let pf := constr:(ltac:(tac) : G) in
abstract exact_no_check pf.

Lemma perm_swap_subst_name a b c: 
  b ≠ c → subst_name c b a = perm_swap ⟨ a, b ⟩ c.
Proof.
  intros; unfold subst_name; simpl;
  destruct (_ =n _); repeat destruct (decide (_ = _)); subst; auto;
  try congruence.
Qed.

Lemma action_lam a b c t: ⟨a,b⟩ • Lam (c, t) = Lam (⟨a,b⟩•c, ⟨a,b⟩•t).
Proof. unfold action; simpl; reflexivity. Qed.

Lemma action_app a b m n: ⟨a,b⟩ • App m n = App (⟨a,b⟩•m) (⟨a,b⟩•n).
Proof. unfold action; simpl; reflexivity. Qed.

Lemma perm_app p m n: p • App m n = App (p•m) (p•n).
Admitted.

Lemma perm_lam p a t: p • Lam (a, t) = Lam (p•a, p•t).
Admitted.

Lemma action_subst a b t: b ∉ atm1 t → (subst t b a) = ⟨a, b⟩ • t.
Proof.
  intros; induction t using term_ind_general.
  - unfold action; simpl; unfold action, name_action; rewrite perm_swap_subst_name;
    auto; set_solver.
  - simpl in *; rewrite action_app; f_equal; [apply IHt1 | apply IHt2]; set_solver.
  - simpl in *; rewrite action_lam; do 2 f_equal; [apply perm_swap_subst_name | apply IHt]; set_solver.
Qed.

Section AlphaStructural.
  Context `{Nominal X} (A: NameSet)
    (fvar : Name →ₛ X) (fapp : (X * X) →ₛ X) (flam : [𝔸]X →ₛ X) {lamFCB : FCB flam}.

  Local Lemma ft_flam (Fm: Perm →ₛ X) a p (Sp: NameSet): 
    ∃ c : Name, (c ∉ Sp) ∧ 
    c # flam [c](Fm (⟨ a, c ⟩ + p)).
  Proof.
    destruct (exist_fresh (Sp ∪ support flam)) as [w Hw]; exists w; split.
    - set_solver.
    - destruct lamFCB as [d [? Hd]].
      specialize (Hd [d](⟨d,w⟩•(Fm (⟨a,w⟩ + p)))).
      apply ((fresh_equivariant ⟨d,w⟩ _ _)) in Hd; rewrite perm_swap_left in Hd.
      rewrite <-(fresh_fixpoint d w flam), fsupp_action, <-perm_inv, nabs_action, name_action_right;
      [apply Hd | |]; apply support_fresh; set_solver.
  Qed.

  Definition g_var (a: Name): Perm →ₛ X.
    refine (λₛ⟦ support fvar ∪ support a ∪ A⟧ p : Perm, fvar (p • a)).
  Proof.
    - eabstract (intros ? ? HH; rewrite HH; reflexivity).
    - abstract (intros w z [[]%not_elem_of_union]%not_elem_of_union [[]%not_elem_of_union]%not_elem_of_union p; 
      unfold action at 3; unfold perm_action;
      rewrite <-2!gact_compat, <-perm_inv, (fresh_fixpoint _ _ a);
        try (apply support_fresh; assumption);
        rewrite perm_inv at 2; rewrite <-fsupp_action, fresh_fixpoint;
          try (apply support_fresh; assumption); reflexivity).
  Defined.

  Definition g_app (Fm Fn: Perm →ₛ X): Perm →ₛ X.
    refine (λₛ⟦ support fapp ∪ support Fm ∪ support Fn ∪ A⟧ p, fapp (Fm p, Fn p)).
  Proof.
    - eabstract (intros ? ? HH; rewrite HH; reflexivity).
    - abstract (intros w z [[[]%not_elem_of_union]%not_elem_of_union]%not_elem_of_union [[[]%not_elem_of_union]%not_elem_of_union]%not_elem_of_union p;
      rewrite <-(fresh_fixpoint w z Fm) at 1; try (apply support_fresh; assumption);
      rewrite <-(fresh_fixpoint w z Fn) at 1; try (apply support_fresh; assumption);
      rewrite <-2!fun_equivar, <-prod_act; rewrite perm_inv at 2; rewrite <-fsupp_action;
      rewrite fresh_fixpoint; try (apply support_fresh; assumption); reflexivity).
  Defined.

  Definition g_lam (a: Name) (m: Term) (Fm: Perm →ₛ X): Perm →ₛ X.
    refine (
      λₛ⟦ support flam ∪ support a ∪ support (Fm) ∪ A ⟧ p,
        let h: Name →ₛ X := λₛ⟦support flam ∪ support a ∪ support m ∪ support (Fm) ∪ support p ∪ A ⟧ a', (flam [a'](Fm (⟨a,a'⟩ + p))) in
        h (fresh (support h))
    ).
    all: swap 1 2.
    - intros w z Hw Hz p; cbn zeta.
      set (g := (λₛ⟦ _ ⟧ a' : Name, flam [a'](Fm (⟨ a, a' ⟩ + (⟨ w, z ⟩ • p))))).
      set (h := (λₛ⟦ _ ⟧ a' : Name, flam [a'](Fm (⟨ a, a' ⟩ + p)))).
      destruct (exist_fresh (support flam ∪ support a ∪ support m ∪ support (Fm) ∪ support w ∪ support z ∪ support (⟨ w, z ⟩ • p) ∪ support p ∪ A)) as [b Hb].
      rewrite (freshness_theorem g (fresh (support g)) b), (freshness_theorem h (fresh (support h)) b);
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
      - intros x y Hxy; cbn zeta; set (a' := fresh _); set (b' := fresh _).
        set (g := (λₛ⟦ _ ⟧ _ : Name, flam [_](Fm (⟨ a, _ ⟩ + x)))).
        set (h := (λₛ⟦ _ ⟧ _' : Name, flam [_](Fm (⟨ a, _ ⟩ + y)))).
        destruct (exist_fresh (support flam ∪ support a ∪ support m ∪ support (Fm) ∪ support x ∪ support y ∪ support a' ∪ support b' ∪ A)) as [c Hc];
        rewrite (freshness_theorem g a' c), (freshness_theorem h b' c);
        try (apply fresh_support_fresh); try (apply support_fresh; subst h g; unfold support at 1; simpl; split_union; repeat (apply not_elem_of_union; split; try eauto));
        try (subst; simpl; apply ft_flam);
        simpl; apply fsupp_equiv, nabs_inv, fsupp_equiv, grp_op_proper; auto.
  Unshelve. 
    eabstract (intros w z Hw Hz b;
    rewrite <-(fresh_fixpoint w z flam) at 2; try (apply support_fresh; set_solver);
    rewrite fsupp_action, <-perm_inv, nabs_action; apply gact_proper, fsupp_equiv; auto;
    rewrite (fun_equivar (⟨w,z⟩) (Fm)), (fresh_fixpoint w z (Fm)); try (apply support_fresh; set_solver);
    rewrite perm_distr_3; set_solver).
  Defined.

  Fixpoint perm_alpha_rec (t: Term) : (Perm →ₛ X) :=
    match t with
    | Var a => g_var a
    | App m n => g_app (perm_alpha_rec m) (perm_alpha_rec n)
    | Lam am => let (a, m) := am in g_lam a m (perm_alpha_rec m)
    end.

  Lemma perm_alpha_rec_app (m n: Term):
    perm_alpha_rec (App m n) = g_app (perm_alpha_rec m) (perm_alpha_rec n).
  Proof. simpl; reflexivity. Qed.

  Lemma perm_alpha_rec_lam a (m: Term):
    perm_alpha_rec (Lam (a,m)) = g_lam a m (perm_alpha_rec m).
  Proof. simpl; reflexivity. Qed.

  Lemma alpha_rec_perm (t: Term):
    ∀ (p q: Perm), perm_alpha_rec t (q + p) ≡ perm_alpha_rec (q • t) p.
  Proof. 
    induction t using term_ind_general; intros.
    - simpl; rewrite gact_compat; reflexivity.
  Admitted.

  Theorem perm_alpha_rec_respectfull (m n : Term) :
    aeq m n → perm_alpha_rec m ≡ perm_alpha_rec n.
  Proof.
    induction 1.
    - simpl; unfold g_var; reflexivity.
    - simpl; unfold g_app; unfold equiv, fun_supp_equiv; intro p; simpl.
      rewrite IHaeq1, IHaeq2; reflexivity.
    - simpl; unfold g_lam, equiv, fun_supp_equiv; intros p; simpl.
      set (s1 := support flam ∪ support a ∪ support m ∪ support (perm_alpha_rec m) ∪ support p ∪ A);
      set (s2 := support flam ∪ support b ∪ support n ∪ support (perm_alpha_rec n) ∪ support p ∪ A).
      set (h1 := (λₛ⟦ s1 ⟧ a' : Name, flam [a'](perm_alpha_rec m (⟨ a, a' ⟩ + p))));
      set (h2 := (λₛ⟦ s2 ⟧ a' : Name, flam [a'](perm_alpha_rec n (⟨ b, a' ⟩ + p)))).
      assert (HH1: flam [fresh (support h1)](perm_alpha_rec m (⟨ a, fresh (support h1) ⟩ + p)) = h1 (fresh (support h1))).
      { subst h1 s1; reflexivity. }
      assert (HH2: flam [fresh (support h2)](perm_alpha_rec n (⟨ b, fresh (support h2) ⟩ + p)) = h2 (fresh (support h2))).
      { subst h2 s2; reflexivity. }
      rewrite HH1, HH2; clear HH1 HH2.
      destruct (exist_fresh (support a ∪ support b ∪ atm1 m ∪ atm1 n ∪ support h2 ∪ support h1 ∪ support flam)) as [w Hw].
      rewrite (freshness_theorem h1 (fresh (support h1)) w), (freshness_theorem h2 (fresh (support h2)) w).
      + subst h1 h2; simpl; apply fsupp_equiv; rewrite !alpha_rec_perm;
        apply name_abstraction_inv; left; split; auto.
        unfold equiv,fun_supp_equiv in H2.
        rewrite <-!action_subst; [apply H2 | |]; set_solver.
      + apply ft_flam.
      + apply fresh_support_fresh.
      + apply support_fresh; set_solver.
      + apply ft_flam.
      + apply fresh_support_fresh.
      + apply support_fresh; set_solver.
  Qed.

  Instance: Proper (aeq ==> equiv) (perm_alpha_rec).
  Proof. repeat intro; apply perm_alpha_rec_respectfull. assumption. Qed.

  Definition alpha_rec (t: Term) := perm_alpha_rec t ɛ.

  Lemma alpha_rec_var a : 
    alpha_rec (Var a) = fvar a.
  Proof. unfold alpha_rec; simpl; rewrite gact_id; auto. Qed.
  
  Lemma alpha_rec_app (m n: Term):
    alpha_rec (App m n) = fapp (alpha_rec m, alpha_rec n).
  Proof. unfold alpha_rec; simpl; reflexivity. Qed.

  Lemma alpha_rec_lam a m:
    let h := fresh (support flam ∪ support a ∪ support m ∪ support (perm_alpha_rec m) ∪ A) in
    alpha_rec (Lam [a]m) ≡ flam [h](alpha_rec (⟨a,h⟩•m)).
  Proof.
    intros; unfold alpha_rec; simpl; unfold support at 1; simpl.
    set (b := fresh _).
    assert (HH: h = b). { subst h b; unfold support; simpl; apply fresh_proper; set_solver. } 
    apply fsupp_equiv, name_abstraction_inv; left; split.
    - auto. 
    - rewrite HH, alpha_rec_perm; reflexivity.
  Qed.

  (* Lemma support_alpha m: support (perm_alpha_rec m) ⊆ support fvar ∪ support fapp ∪ support flam ∪ fv m.
  Proof.
    induction m using term_ind_general; simpl; unfold support at 1; admit.
    Admitted.
    (* - simpl. set_solver.
    - set_solver.
    - simpl. Search (_ ⊆ _ ∪ _). *) *)

  (* Lemma alpha_rec_lam_exists m:
    ∀ a, a ∉ (support fvar ∪ support fapp ∪ support flam) → 
    alpha_rec (Lam [a]m) ≡ flam [a](alpha_rec m).
  Proof.
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

  Lemma alpha_rec_lam_exists_abs m:
    ∃ L: NameSet, ∀ a, a ∉ L → alpha_rec (Lam (a,m)) ≡ flam [a](alpha_rec m).
  Proof.
    exists (support flam ∪ support m ∪ support (perm_alpha_rec m)); intros.
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
  Qed.

  Lemma alpha_rec_respectfull m n : 
    aeq m n → alpha_rec m ≡ alpha_rec n.
  Proof. intros; unfold alpha_rec; apply perm_alpha_rec_respectfull; assumption. Qed.
End AlphaStructural.

Lemma var_perm a p: p • (Var a) = Var (p • a).
Proof. auto. Qed.

Lemma app_perm m n p: p • (App m n) = App (p • m) (p • n).
Proof. auto. Qed.

Lemma lam_perm a m p: p • (Lam (a,m)) = Lam (p • a, p • m).
Proof. auto. Qed.

Lemma empty_perm (t: Term): ɛ • t = t.
Proof. Admitted.


(* Copello *)
Definition term_rect_perm_general (P : Term → Type)
  (fvar : ∀ a p, P (p • (Var a)))
  (fapp : ∀ m, (∀ p, P (p • m)) → ∀ n, (∀ p, P (p • n)) → (∀ p, P (p • App m n)))
  (flam : ∀ a m, (∀ p, P (p • m)) → (∀ p, P (p • (Lam (a,m))))): 
  ∀ t p, P (p • t).
Proof. 
  induction t using term_rect_general; intros.
  - intros; apply fvar.
  - eapply fapp; eauto.
  - eapply flam; eapply IHt.
Qed.

Class αCompat `{Equiv X} (P: X → Prop) := {
  compat: ∀ m n, m ≡ n → P m → P n
}.

#[export] Instance αCompatProper `{αCompat X P}: Proper (equiv ==> impl) P.
Proof. intros ? ? HH ?; eapply compat; eauto. Qed.

#[export] Instance αCompatProperFlip `{αCompat X P}: Proper (equiv ==> flip impl) P.
Proof. intros ? ? HH ?; eapply compat; eauto. Admitted.

Lemma lam_abs_equiv (am bn: [𝔸]Term): am ≡ bn → Lam am ≡ Lam bn.
Proof. Admitted. 

Lemma alpha_ind_lam_aux:
  ∀ P: Term → Prop, αCompat P →
    ∀ L: NameSet, (∀ b m, b ∉ L → (∀ p, P (p • m)) → P (Lam [b]m)) →
      ∀ a m, (∀ p, P (p • m)) → P (Lam [a]m).
Proof.
  intros ? ? L HL a m ?.
  destruct (exist_fresh (support (Lam [a]m) ∪ support a ∪ L)) as
    [z [[HLam ?]%not_elem_of_union ?]%not_elem_of_union].
  apply compat with (Lam [z](⟨a,z⟩•m)).
  - symmetry; apply lam_abs_equiv, name_abstraction_rename, support_fresh;
      unfold support in HLam; simpl in *; apply not_elem_of_difference in HLam as [];
      [assumption | set_solver].
  - apply HL; [assumption |]; intros; rewrite gact_compat; auto.
Qed.

Definition alpha_ind:
  ∀ P : Term → Prop, αCompat P →
    (∀ a, P (Var a)) →
    (∀ m n, P m → P n → P (App m n)) →
    {L: NameSet | ∀ a m, a ∉ L → P m → P (Lam [a]m)} →
  ∀ t, P t.
Proof.
  intros P αP Hvar Happ [L Habs] t; rewrite <-gact_id; apply term_rect_perm_general.
  - intros; rewrite var_perm; apply Hvar.
  - intros; rewrite app_perm; auto.
  - intros; rewrite lam_perm; apply (alpha_ind_lam_aux _ αP) with L; intros.
    + apply Habs; [| rewrite <-gact_id]; auto.  
    + rewrite gact_compat; apply H.
Qed.

Section TermLength.

  From Nominal Require Import Instances.Nat.
  
  Fixpoint term_length (t: Term): nat :=
    match t with
    | Var a => 1
    | App m n => (term_length m) + (term_length n)
    | Lam (a,m) => 1 + (term_length m)
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

  (* Lemma length_equal:
    ∀ t, term_length t = alpha_rec length_fvar length_fapp length_flam (lamFCB := length_flam_fcb) t.
  Proof.
    apply alpha_ind.
    - apply Build_αCompat; intros; inversion H; subst;
      erewrite alpha_rec_respectfull, term_lenght_respectfull; eauto; symmetry.
      + assumption.
      + constructor; assumption.
    - intros; rewrite alpha_rec_var; simpl; reflexivity.
    - intros ? ? A B; rewrite alpha_rec_app; simpl in *; rewrite A, B; reflexivity.
    - eexists. intros. pose proof alpha_rec_lam_exists.
      + simpl; auto.
      + eapply H.   
    
    exists ∅. intros. rewrite alpha_rec_lam. set (w := fresh _). simpl in *.
    
    destruct (alpha_rec_lam_exists ∅ length_fvar length_fapp length_flam (lamFCB := length_flam_fcb) m).
      rewrite H1. 



    - rewrite alpha_rec_app, <-IHt1, <-IHt2; simpl; reflexivity.
    - pose proof (alpha_rec_lam_exists_abs ∅ length_fvar length_fapp length_flam (lamFCB := length_flam_fcb)) t.
      destruct H as [L ?].  rewrite H.
      + simpl; rewrite IHt; reflexivity.
      +  *)

End TermLength.