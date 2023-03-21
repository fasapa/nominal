From Nominal Require Import Nominal Fresh.
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
| AeqAbs: ∀ (a b: Name) (m n: Term), ∀ c,
    (c <> a ∧ c <> b) → (c ∉ atm1 m ∧ c ∉ atm1 n) →
    aeq (subst m c a) (subst n c b) → aeq (Lam (a,m)) (Lam (b,n)).

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

(* Theorem freshness_theorem `{Nominal X} (f: Name →ₛ X): 
  (∃ (c: Name), c ∉ support f ∧ c # (f c)) → 
  ∀ a b, a # f → b # f → f a ≡ f b.
Proof.

They are both provable
*)

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

From Nominal Require Import Alpha NameAbstraction.

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

Section AlphaStructural.
  Context `{Nominal X} (A: NameSet)
    (fvar : Name →ₛ X) (fapp : (X * X) →ₛ X) (flam : [𝔸]X →ₛ X) {lamFCB : FCB flam}.

  Definition supp_fvar (a: Name): Perm →ₛ X.
    refine (λₛ⟦ support fvar ∪ support a ∪ A⟧ p : Perm, fvar (p • a)).
  Proof.
    - intros ? ? HH; rewrite HH; reflexivity.
    - intros w z [[]%not_elem_of_union]%not_elem_of_union [[]%not_elem_of_union]%not_elem_of_union p; 
      unfold action at 3; unfold perm_action;
      rewrite <-2!gact_compat, <-perm_inv, (fresh_fixpoint _ _ a);
        try (apply support_fresh; assumption);
        rewrite perm_inv at 2; rewrite <-fsupp_action, fresh_fixpoint;
          try (apply support_fresh; assumption); reflexivity.
  Defined.

  Definition supp_fapp (Fm Fn: Perm →ₛ X): Perm →ₛ X.
    refine (λₛ⟦ support fapp ∪ support Fm ∪ support Fn ∪ A⟧ p, fapp (Fm p, Fn p)).
  Proof.
    - intros ? ? HH; rewrite HH; reflexivity.
    - abstract (intros w z [[[]%not_elem_of_union]%not_elem_of_union]%not_elem_of_union [[[]%not_elem_of_union]%not_elem_of_union]%not_elem_of_union p;
      rewrite <-(fresh_fixpoint w z Fm) at 1; try (apply support_fresh; assumption);
      rewrite <-(fresh_fixpoint w z Fn) at 1; try (apply support_fresh; assumption);
      rewrite <-2!fun_equivar, <-prod_act; rewrite perm_inv at 2; rewrite <-fsupp_action;
      rewrite fresh_fixpoint; try (apply support_fresh; assumption); reflexivity).
  Defined.

  Definition supp_flam (a: Name) (Fm: Perm →ₛ X): Perm →ₛ X.
    refine (
      λₛ⟦ support flam ∪ support a ∪ support Fm ∪ A ⟧ p,
        let h: Name →ₛ X := λₛ⟦support flam ∪ support Fm ∪ support a ∪ support p ∪ A ⟧ a', (flam [a'](Fm (⟨a,a'⟩ + p))) in
        h (fresh (support h))
    ).
    all: swap 1 2.
    - intros w z Hw Hz p; cbn zeta.
    set (g := (λₛ⟦ support flam ∪ support Fm ∪ support a ∪ support (⟨ w, z ⟩ • p) ∪ A ⟧ a' : Name, flam [a'](Fm (⟨ a, a' ⟩ + (⟨ w, z ⟩ • p))))).
    set (h := (λₛ⟦ support flam ∪ support Fm ∪ support a ∪ support p ∪ A ⟧ a' : Name, flam [a'](Fm (⟨ a, a' ⟩ + p)))).
    destruct (exist_fresh (support flam ∪ support Fm ∪ support a ∪ support w ∪ support z ∪ support (⟨ w, z ⟩ • p) ∪ support p ∪ A)) as [b Hb].
    rewrite (freshness_theorem g (fresh (support g)) b), (freshness_theorem h (fresh (support h)) b);
    try (apply fresh_support_fresh); try (apply support_fresh; subst h g; unfold support at 1; simpl; set_solver).
    all: swap 1 2. all: swap 2 3.
    + exists b; split.
      * subst h; unfold support; simpl; set_solver.
      * subst h; simpl; destruct lamFCB as [c [? Hc2]].
         specialize (Hc2 [c](⟨ c, b ⟩ • (Fm (⟨ a, b ⟩ + p)))).
         apply ((fresh_equivariant ⟨c,b⟩ _ _)) in Hc2; rewrite perm_swap_left in Hc2.
         rewrite <-(fresh_fixpoint c b flam), fsupp_action, <-perm_inv, nabs_action, name_action_right;
         [apply Hc2 | |]; apply support_fresh; set_solver.
    + exists b; split.
      * subst g; unfold support; simpl; set_solver.
      * subst g; simpl; destruct lamFCB as [c [? Hc2]].
        specialize (Hc2 [c](⟨ c, b ⟩ • (Fm (⟨ a, b ⟩ + (⟨ w, z ⟩ • p))))).
        apply ((fresh_equivariant ⟨c,b⟩ _ _)) in Hc2; rewrite perm_swap_left in Hc2.
        rewrite <-(fresh_fixpoint c b flam), fsupp_action, <-perm_inv, nabs_action, name_action_right;
        [apply Hc2 | |]; apply support_fresh; set_solver.
    + subst g h; simpl.
      assert (HH: flam [b](Fm (⟨a,b⟩+(⟨w,z⟩•p))) ≡ flam [b]((⟨w,z⟩•Fm) (⟨w,z⟩•⟨a,b⟩+p))). {
      apply fsupp_equiv, nabs_inv. 
      rewrite perm_distr_1, perm_distr,<-(fresh_fixpoint w z Fm) at 1;
      try reflexivity; try (apply support_fresh); set_solver.
      } rewrite HH; clear HH.
      rewrite <-(fresh_fixpoint w z b) at 1; try (apply support_fresh; set_solver).
      assert (HH: flam [⟨w,z⟩•b]((⟨w,z⟩•Fm) (⟨w,z⟩•⟨a,b⟩+p)) ≡ flam ([⟨w,z⟩•b](⟨w,z⟩•(Fm (⟨a,b⟩+p))))). {
      apply fsupp_equiv, nabs_inv. rewrite fun_equivar; reflexivity.
      } rewrite HH; clear HH.
      rewrite <-nabs_action,<-fsupp_action, fresh_fixpoint; try (apply support_fresh; set_solver).
      reflexivity.
    - intros x y Hxy; cbn zeta; set (a' := fresh _); set (b' := fresh _).
      set (g := (λₛ⟦ _ ⟧ _ : Name, flam [_](Fm (⟨ a, _ ⟩ + x)))).
      set (h := (λₛ⟦ _ ⟧ _' : Name, flam [_](Fm (⟨ a, _ ⟩ + y)))).
      destruct (exist_fresh (support flam ∪ support Fm ∪ support a ∪ support x ∪ support y ∪ support a' ∪ support b' ∪ A)) as [c Hc];
      repeat (apply not_elem_of_union in Hc as [Hc ?]);
      rewrite (freshness_theorem g a' c), (freshness_theorem h b' c);
      try (apply fresh_support_fresh); try (apply support_fresh; subst h g; unfold support at 1; simpl; set_solver).
      + simpl; apply fsupp_equiv, nabs_inv, fsupp_equiv, grp_op_proper; auto.
      + exists c; split.
        * subst h; unfold support; simpl; set_solver.
        * subst h; simpl; destruct lamFCB as [d [? Hd]].
           specialize (Hd [d](⟨d,c⟩•(Fm (⟨a,c⟩ + y)))).
           apply ((fresh_equivariant ⟨d,c⟩ _ _)) in Hd; rewrite perm_swap_left in Hd.
           rewrite <-(fresh_fixpoint d c flam), fsupp_action, <-perm_inv, nabs_action, name_action_right;
           [apply Hd | |]; apply support_fresh; set_solver.
      + exists c; split.
        * subst g; unfold support; simpl; set_solver.
        * subst g; simpl; destruct lamFCB as [d [? Hd]].
           specialize (Hd [d](⟨d,c⟩•(Fm (⟨a,c⟩ + x)))).
           apply ((fresh_equivariant ⟨d,c⟩ _ _)) in Hd; rewrite perm_swap_left in Hd.
           rewrite <-(fresh_fixpoint d c flam), fsupp_action, <-perm_inv, nabs_action, name_action_right;
           [apply Hd | |]; apply support_fresh; set_solver.
  Unshelve. 
    intros w z Hw Hz b.
    rewrite <-(fresh_fixpoint w z flam) at 2; try (apply support_fresh; set_solver).
    rewrite fsupp_action, <-perm_inv, nabs_action; apply gact_proper, fsupp_equiv; auto.
    rewrite (fun_equivar (⟨w,z⟩) Fm), (fresh_fixpoint w z Fm); try (apply support_fresh; set_solver).
    rewrite perm_distr_3; set_solver.
  Defined.

  Fixpoint perm_alpha_rec (t: Term) : (Perm →ₛ X) :=
    match t with
    | Var a => supp_fvar a
    | App m n => supp_fapp (perm_alpha_rec m) (perm_alpha_rec n)
    | Lam am => let (a, m) := am in supp_flam a (perm_alpha_rec m) 
    end.
End AlphaStructural.

Section Respectfull.
  Context `{Nominal X} (A: NameSet)
           (fvar : Name →ₛ X) (fapp : (X * X) →ₛ X) (flam : [𝔸]X →ₛ X) {lamFCB : FCB flam}.

  Let alpha_rec (t: Term) := 
    perm_alpha_rec A fvar fapp flam (lamFCB := lamFCB) t.

  Lemma perm_alpha_rec_var (a: Name):
    alpha_rec (Var a) = supp_fvar A fvar a.
  Proof. simpl; reflexivity. Qed.

  Lemma perm_alpha_rec_app (m n: Term):
    alpha_rec (App m n) = supp_fapp A fapp (alpha_rec m) (alpha_rec n).
  Proof. simpl; reflexivity. Qed.

  Lemma perm_alpha_rec_lam (a: Name) (m: Term):
    alpha_rec (Lam [a]m) = 
    supp_flam A flam (lamFCB := lamFCB) a (alpha_rec m).
  Proof. simpl; reflexivity. Qed.

  Theorem perm_alpha_rec_respectfull (m n : Term) :
    aeq m n → alpha_rec m ≡ alpha_rec n.
  Proof.
    induction 1.
    - rewrite !perm_alpha_rec_var; unfold supp_fvar; reflexivity.
    - simpl; unfold supp_fapp; unfold equiv, fun_supp_equiv; intro p; simpl.
      rewrite IHaeq1, IHaeq2; reflexivity.
    - simpl; unfold supp_flam; unfold equiv, fun_supp_equiv; intro p; simpl.
      apply fsupp_equiv. set (a' := fresh _); set (b' := fresh _). admit.
  Admitted.
End Respectfull.