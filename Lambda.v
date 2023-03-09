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

Inductive aeq: Term → Term → Prop :=
| AeqVar: ∀ a, aeq (Var a) (Var a)
| AeqApp: ∀ m n m' n', aeq m m' → aeq n n' → aeq (App m n) (App m' n')
| AeqAbs: ∀ (a b c: Name) (m n: Term),
    (c <> a ∧ c <> b) → (c ∉ atm1 m ∧ c ∉ atm1 n) →
    aeq (subst m c a) (subst n c b) → aeq (Lam (a,m)) (Lam (b,n)).

(* Necessario alguma relacao proper sobre os argumentos de aeq para
  facilitar reescrita *)

Lemma aeq_subst: ∀ m n a b, aeq m n → aeq (subst m a b) (subst n a b).
Proof. Admitted.

#[export] Instance subst_proper: Proper (aeq ==> eq ==> eq ==> aeq) subst.
Proof. repeat intro; subst; apply aeq_subst; auto. Qed.

#[export] Instance: Equiv Term := aeq.
#[export] Instance: Reflexive aeq.
Proof.
  intro x; induction x using term_ind_general.
  - constructor.
  - constructor; auto.
  - econstructor.
    + (* facil, basta pegar um C diferente *) admit.
    + (* facil, basta pegar um C diferente *) admit.
    + apply aeq_subst; auto.
Admitted.

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

Lemma fun_eq `{Nominal X, Nominal Y} x y (f: X →ₛ Y): x ≡ y → f x ≡ f y.
Proof. intros XY; rewrite XY; reflexivity. Qed.

Definition FCB `{Nominal X, Nominal Y} (f: X →ₛ Y) :=
  { a | a ∉ (support f) ∧ (∀ x: X, a # (f x)) }.
 
Lemma perm_distr w z (p q: Perm): ⟨w,z⟩ • (p + q) ≡ (⟨w,z⟩ • p) + (⟨w,z⟩ • q).
Proof. 
  unfold action, perm_action; rewrite <-perm_inv, !grp_assoc. 
  assert (HH: ⟨ w, z ⟩ + p + ⟨ w, z ⟩ + ⟨ w, z ⟩ + q + ⟨ w, z ⟩ ≡ ⟨ w, z ⟩ + p + (⟨ w, z ⟩ + ⟨ w, z ⟩) + q + ⟨ w, z ⟩).
  { rewrite !grp_assoc; reflexivity. }
  rewrite HH; clear HH.
  rewrite perm_duplicate.
  assert (HH: ⟨ w, z ⟩ + p + ɛ + q + ⟨ w, z ⟩ ≡ ⟨ w, z ⟩ + p + (ɛ + (q + ⟨ w, z ⟩))).
  { rewrite !grp_assoc; reflexivity. } rewrite HH; clear HH.
  rewrite grp_left_id, !grp_assoc; reflexivity.
Qed.

Lemma fun_1 `{Nominal X, Nominal Y} (p : Perm) (f: X →ₛ Y) (x : X):
  p • (f x) ≡ (p • f)(p • x).
Proof.
  unfold action at 2; unfold fun_supp_act; simpl. 
  rewrite perm_left_inv; reflexivity.
Qed.

Lemma name_action_left (a b: Name) : ⟨ a, b ⟩ • a ≡ b.
Proof. unfold action, name_action; apply perm_swap_left. Qed.

Lemma name_action_right (a b: Name) : ⟨ a, b ⟩ • b ≡ a.
Proof. unfold action, name_action; apply perm_swap_right. Qed.

Theorem fresh_2 `{Nominal X} (f: Name →ₛ X): 
  (∃ (a: Name), a ∉ support f ∧ a # (f a)) → 
  ∀ b c, b # f ∧ c # f → f b ≡ f c.
Proof. 
  intros [a []] ? ? []. 
  rewrite <-(fresh_fixpoint a b f) at 1; auto; try (apply support_fresh; assumption).
  rewrite <-(fresh_fixpoint a c f) at 2; auto; try (apply support_fresh; assumption).
  unfold action, fun_supp_act; simpl; rewrite <-!perm_inv, !name_action_right.
  destruct (decide (a = b)), (decide (a = c)); subst.
  - rewrite perm_action_equal; reflexivity.
  - rewrite perm_action_equal; rewrite fresh_fixpoint.
    + reflexivity.
    + assumption.
    + apply fresh_fun_supp; auto; apply name_neq_fresh_iff, not_eq_sym; assumption.
  - rewrite perm_action_equal; rewrite fresh_fixpoint.
    + reflexivity.
    + assumption.
    + apply fresh_fun_supp; auto; apply name_neq_fresh_iff, not_eq_sym; assumption.
  - rewrite 2fresh_fixpoint; try reflexivity; try assumption;
      apply fresh_fun_supp; auto; apply name_neq_fresh_iff, not_eq_sym; assumption.
Qed.

Lemma fresh_respectfull (A B: NameSet): A ≡ B → fresh A ≡ fresh B.
Proof. intros AB; rewrite AB; reflexivity. Qed.

From Nominal Require Import Alpha NameAbstraction.

Definition perm_rect_iterator_supported_abstraction `{Nominal X}
  (A: NameSet)
  (fvar : Name →ₛ X) (* support fvar ⊂ A *)
  (fapp : (X * X) →ₛ X)
  (flam : [𝔸]X →ₛ X) 
  {lamFCB : FCB flam} : Term → (Perm →ₛ X).
Proof.
  refine(
    fix F (t: Term) :=
      match t with
      | Var a => 
        λₛ⟦ support fvar ∪ support a ⟧ p, fvar (p • a)
      | App m n => 
        λₛ⟦ support fapp ∪ support (F m) ∪ support (F n) ⟧ p, fapp ((F m) p, (F n) p)
      | Lam am => let (a, m) := am in 
        λₛ⟦ support flam ∪ support a ∪ support (F m) ⟧ p,
          let h: Name →ₛ X := λₛ⟦support flam ∪ support (F m) ∪ support a ∪ support p ∪ A ⟧ a', (flam [a'](F m (⟨a,a'⟩ + p))) in
          h (fresh (support h)) 
      end
  ).
  all: swap 5 6.
  - repeat intro; rewrite H1; reflexivity.
  - abstract (intros w z []%not_elem_of_union []%not_elem_of_union p; 
    unfold action at 3; unfold perm_action;
    rewrite <-2!gact_compat, <-perm_inv, (fresh_fixpoint _ _ a);
      try (apply support_fresh; assumption);
      rewrite perm_inv at 2; rewrite <-fsupp_action, fresh_fixpoint;
        try (apply support_fresh; assumption); reflexivity).
  - repeat intro; rewrite H1; reflexivity.
  - abstract (intros w z [[]%not_elem_of_union ?]%not_elem_of_union [[]%not_elem_of_union ?]%not_elem_of_union p;
    rewrite <-(fresh_fixpoint w z (F m)) at 1; try (apply support_fresh; assumption);
    rewrite <-(fresh_fixpoint w z (F n)) at 1; try (apply support_fresh; assumption);
    rewrite <-2!fun_1, <-prod_act; rewrite perm_inv at 2; rewrite <-fsupp_action;
    rewrite fresh_fixpoint; try (apply support_fresh; assumption); reflexivity).
  - intros w z Hw Hz p; cbn zeta.
    set (g := (λₛ⟦ support flam ∪ support (F m) ∪ support a ∪ support (⟨ w, z ⟩ • p) ∪ A ⟧ a' : Name, flam [a'](F m (⟨ a, a' ⟩ + (⟨ w, z ⟩ • p))))).
    set (h := (λₛ⟦ support flam ∪ support (F m) ∪ support a ∪ support p ∪ A ⟧ a' : Name, flam [a'](F m (⟨ a, a' ⟩ + p)))).
    destruct (exist_fresh (support flam ∪ support (F m) ∪ support a ∪ support w ∪ support z ∪ support (⟨ w, z ⟩ • p) ∪ support p ∪ A)) as [b Hb].
    assert (HH1: (∃ (b: Name), b ∉ (support flam ∪ support (F m) ∪ support a ∪ support (⟨ w, z ⟩ • p) ∪ A) ∧ b # (g b))). {
       exists b; split.
       - set_solver.
       - subst g; simpl; destruct lamFCB as [c [Hc1 Hc2]].
         specialize (Hc2 [c](⟨ c, b ⟩ • (F m (⟨ a, b ⟩ + (⟨ w, z ⟩ • p))))).
         apply ((fresh_equivariant ⟨c,b⟩ _ _)) in Hc2; rewrite perm_swap_left in Hc2.
         assert (HH: (⟨ c, b ⟩•(flam [c](⟨ c, b ⟩ • F m (⟨ a, b ⟩ + (⟨ w, z ⟩ • p))))) ≡ flam [b](F m (⟨a,b⟩ + (⟨ w, z ⟩ • p)))).
         { rewrite fun_1, nabs_action, name_action_left, (fresh_fixpoint _ _ flam).
            + apply fun_eq, nabs_inv, perm_action_duplicate. 
            + apply support_fresh; assumption.
            + apply support_fresh; set_solver.
         }
         rewrite <-HH; apply Hc2.
    }
    assert (HH2: (∃ (b: Name), b ∉ (support flam ∪ support (F m) ∪ support a ∪ support p ∪ A) ∧ b # (h b))). { 
      exists b; split.
      - set_solver.  
      - subst h; simpl; destruct lamFCB as [c [Hc1 Hc2]].
        specialize (Hc2 [c](⟨ c, b ⟩ • (F m (⟨ a, b ⟩ + p)))).
        apply ((fresh_equivariant ⟨c,b⟩ _ _)) in Hc2; rewrite perm_swap_left in Hc2.
        assert (HH: (⟨ c, b ⟩ • flam [c](⟨ c, b ⟩ • F m (⟨ a, b ⟩ + p))) ≡ flam [b](F m (⟨ a, b ⟩ + p))). {
          rewrite fun_1, nabs_action, name_action_left, (fresh_fixpoint _ _ flam).
          + apply fun_eq, nabs_inv, perm_action_duplicate.
          + apply support_fresh; assumption.
          + apply support_fresh; set_solver.  
        }
        rewrite <-HH; apply Hc2.
    }
    pose proof fresh_2 as F1; pose proof fresh_2 as F2.
    specialize (F1 g HH1 (fresh (support g)) b). specialize (F2 h HH2 (fresh (support h)) b).
    rewrite F1; try (split; [apply fresh_support_fresh | apply support_fresh; subst g; unfold support at 1; simpl; set_solver]).
    rewrite F2; try (split; [apply fresh_support_fresh | apply support_fresh; subst h; unfold support at 1; simpl; set_solver]). 
    subst g h; simpl.
    clear HH1 HH2 F1 F2.
    assert (HH1: (⟨a,b⟩ + (⟨w, z⟩•p)) ≡ (⟨w, z⟩•⟨a,b⟩) + (⟨w,z⟩•p)). {
      rewrite <-(fresh_fixpoint w z (⟨ a, b ⟩)) at 1. reflexivity.
      - apply support_fresh; unfold support; simpl; apply not_elem_of_union; split.
        + apply not_elem_of_union; split; unfold support,name_support in *; simpl in *;
          set_solver.
        + set_solver.
      - apply support_fresh; unfold support; simpl; apply not_elem_of_union; split.
        + apply not_elem_of_union; split; unfold support,name_support in *; simpl in *;
          set_solver.
        + set_solver.   
    }
    assert (HH2: (⟨w,z⟩•⟨a,b⟩) + (⟨w,z⟩•p) ≡ ⟨w,z⟩•(⟨a,b⟩ + p)). {
      unfold action, perm_action; rewrite <-perm_inv, !grp_assoc.
      assert (HHH2: ⟨ w, z ⟩ + ⟨ a, b ⟩ + ⟨ w, z ⟩ + ⟨ w, z ⟩ + p + ⟨ w, z ⟩ ≡ ⟨ w, z ⟩ + ⟨ a, b ⟩ + (⟨ w, z ⟩ + ⟨ w, z ⟩) + p + ⟨ w, z ⟩). {
        rewrite !grp_assoc; reflexivity.
      }
      rewrite HHH2, perm_duplicate.
      assert (HHH3: ⟨ w, z ⟩ + ⟨ a, b ⟩ + ɛ + p + ⟨ w, z ⟩ ≡ ⟨ w, z ⟩ + ⟨ a, b ⟩ + (ɛ + (p + ⟨ w, z ⟩))). {
        rewrite !grp_assoc; reflexivity.
      }
      rewrite HHH3, grp_left_id, !grp_assoc; reflexivity.
    }
    assert (HH: flam [b](F m (⟨ a, b ⟩ + (⟨ w, z ⟩ • p))) ≡ flam [b]((⟨ w, z ⟩ • F m) (⟨ w, z ⟩ • ⟨ a, b ⟩ + p))). {
      apply fun_eq, nabs_inv; 
      rewrite HH1, HH2.
      rewrite <-(fresh_fixpoint w z (F m)) at 1; try (apply support_fresh; set_solver).
      reflexivity.
    }
    rewrite HH; clear HH1 HH2 HH.
    assert (HH: flam [b]((⟨ w, z ⟩ • F m) (⟨ w, z ⟩ • ⟨ a, b ⟩ + p)) ≡ flam [⟨ w, z ⟩ •b]((⟨ w, z ⟩ • F m) (⟨ w, z ⟩ • ⟨ a, b ⟩ + p))). {
      apply fun_eq. rewrite <-(fresh_fixpoint w z b) at 1; try (apply support_fresh; set_solver).
      reflexivity.
    }
    rewrite HH; clear HH.
    assert (HH: flam [⟨ w, z ⟩•b]((⟨ w, z ⟩ • F m) (⟨ w, z ⟩ • ⟨ a, b ⟩ + p)) ≡ flam ([⟨ w, z ⟩•b](⟨ w, z ⟩•(F m (⟨a, b ⟩ + p))))). {
      apply fun_eq, nabs_inv. rewrite fun_1. reflexivity.
    }
    rewrite HH; clear HH.
    assert (HH: flam [⟨ w, z ⟩ • b](⟨ w, z ⟩ • F m (⟨ a, b ⟩ + p)) ≡ flam (⟨ w, z ⟩•([b](F m (⟨ a, b ⟩ + p))))). {
      apply fun_eq; rewrite nabs_action; reflexivity.
    }
    rewrite HH; clear HH.
    rewrite <-fsupp_action, fresh_fixpoint; try (apply support_fresh; set_solver).
    reflexivity.
Unshelve.
  (* show that h is supported *)
  intros w z Hw Hz b.
  set (T := ⟨ w, z ⟩ • flam [⟨ w, z ⟩ • b](F m (⟨ a, ⟨ w, z ⟩ • b ⟩ + p))).
  rewrite <-(fresh_fixpoint w z flam); try (apply support_fresh; set_solver).
  rewrite fsupp_action, <-perm_inv, nabs_action.
  assert (HH: flam [⟨ w, z ⟩ • b](⟨ w, z ⟩ • F m (⟨ a, b ⟩ + p)) ≡ flam [⟨ w, z ⟩ • b]((⟨ w, z ⟩ • F m) (⟨ w, z ⟩ • ⟨ a, b ⟩ + p))). {
    apply fun_eq, nabs_inv; rewrite (fun_1 (⟨w,z⟩) (F m)). reflexivity.
  }
  rewrite HH; clear HH.
  assert (HH: flam [⟨ w, z ⟩ • b]((⟨ w, z ⟩ • F m) (⟨ w, z ⟩ • ⟨ a, b ⟩ + p)) ≡ flam [⟨ w, z ⟩ • b]((F m (⟨ w, z ⟩ • ⟨ a, b ⟩ + p)))). {  
    apply fun_eq, nabs_inv; rewrite (fresh_fixpoint w z (F m)); try (apply support_fresh; set_solver); reflexivity.
  }
  rewrite HH; clear HH.
  assert (HH: flam [⟨ w, z ⟩ • b](F m (⟨ w, z ⟩ • ⟨ a, b ⟩ + p)) ≡ flam [⟨ w, z ⟩ • b](F m (⟨ a, ⟨ w, z ⟩ • b ⟩ + p))). {
    apply fun_eq, nabs_inv.
    rewrite perm_distr; unfold action at 1; unfold action at 1; unfold perm_action.
    assert (HH: - ⟨ w, z ⟩ + (⟨ a, b ⟩ + ⟨ w, z ⟩) + (- ⟨ w, z ⟩ + (p + ⟨ w, z ⟩)) ≡ (⟨ a, ⟨ w, z ⟩ • b ⟩ + p)). {
      rewrite <-perm_inv, !grp_assoc.
      assert (HH1: ⟨ w, z ⟩ + ⟨ a, b ⟩ + ⟨ w, z ⟩ + ⟨ w, z ⟩ + p + ⟨ w, z ⟩ ≡ ⟨ w, z ⟩ + ⟨ a, b ⟩ + p + ⟨ w, z ⟩). {
         assert (HHH: ⟨ w, z ⟩ + ⟨ a, b ⟩ + ⟨ w, z ⟩ + ⟨ w, z ⟩ + p + ⟨ w, z ⟩ ≡ ⟨ w, z ⟩ + ⟨ a, b ⟩ + (⟨ w, z ⟩ + ⟨ w, z ⟩) + p + ⟨ w, z ⟩). {
         rewrite !grp_assoc; reflexivity. }
         rewrite HHH, perm_duplicate.
         assert (HHH1: ⟨ w, z ⟩ + ⟨ a, b ⟩ + ɛ + p + ⟨ w, z ⟩ ≡ ⟨ w, z ⟩ + ⟨ a, b ⟩ + (ɛ + (p + ⟨ w, z ⟩))). {
          rewrite !grp_assoc; reflexivity.
         } rewrite HHH1, grp_left_id, !grp_assoc; reflexivity.
    }
    rewrite HH1; pose proof (perm_notin_dom_comm w z p) as H1.
    assert (HH2: ⟨ w, z ⟩ + ⟨ a, b ⟩ + p + ⟨ w, z ⟩ ≡ ⟨ w, z ⟩ + ⟨ a, b ⟩ + ⟨ w, z ⟩ + p). {
      assert (HHH: ⟨ w, z ⟩ + ⟨ a, b ⟩ + p + ⟨ w, z ⟩ ≡ ⟨ w, z ⟩ + ⟨ a, b ⟩ + (p + ⟨ w, z ⟩)). {
        rewrite !grp_assoc; reflexivity.
      } rewrite HHH, <-H1; unfold support in *; set_solver.
    }
    rewrite HH2.
    pose proof (perm_comm_distr a b ⟨ w, z ⟩); rewrite perm_swap_neither in H2;
      try (apply not_eq_sym, name_neq_fresh_iff, support_fresh; set_solver).
    assert (HH3: ⟨ w, z ⟩ + ⟨ a, b ⟩ + ⟨ w, z ⟩ + p ≡ ⟨ w, z ⟩ + (⟨ a, b ⟩ + ⟨ w, z ⟩) + p). {
      rewrite !grp_assoc; reflexivity.
    }
    rewrite HH3, H2, !grp_assoc, perm_duplicate, grp_left_id; unfold action. simpl; reflexivity.
  }
  assert (HH1: F m (- ⟨ w, z ⟩ + (⟨ a, b ⟩ + ⟨ w, z ⟩) + (- ⟨ w, z ⟩ + (p + ⟨ w, z ⟩))) ≡ F m (⟨ a, ⟨ w, z ⟩ • b ⟩ + p)). {
    rewrite HH; reflexivity.
  }
  rewrite HH1; reflexivity.
  }
  rewrite HH; subst T; reflexivity.
- repeat intro; cbn zeta. set (a' := fresh _); set (b' := fresh _).
  destruct (exist_fresh (support flam ∪ support (F m) ∪ support a ∪ support x ∪ support y ∪ support a' ∪ support b' ∪ A)) as [c Hc].
  rewrite fresh_2 with (c := c), fresh_2 with (b := b') (c := c).
  + simpl; apply fun_eq, nabs_inv, fun_eq, grp_op_proper; auto.
  + exists c; split.
    * unfold support in *; subst a' b'; simpl in *; set_solver.
    * simpl; destruct lamFCB as [d [Hd1 Hd2]].
      specialize (Hd2 [d](⟨ d, c ⟩ • (F m (⟨ a, c ⟩ + y)))).
      apply ((fresh_equivariant ⟨d,c⟩ _ _)) in Hd2; rewrite perm_swap_left in Hd2.
      assert (HH: (⟨ d, c ⟩ • flam [d](⟨ d, c ⟩ • F m (⟨ a, c ⟩ + y))) ≡ flam [c](F m (⟨ a, c ⟩ + y))). {
        rewrite fun_1, nabs_action, name_action_left, (fresh_fixpoint _ _ flam).
        + apply fun_eq; unfold equiv, name_abstraction_equiv; apply alpha_inv_iff; left;
          split; auto. rewrite perm_action_duplicate; reflexivity.
        + apply support_fresh; assumption.
        + repeat apply not_elem_of_union in Hc as [Hc ?]; apply support_fresh; assumption.
      }
      rewrite <-HH; apply Hd2.
  + split; apply support_fresh; subst b'; unfold support in *; simpl in *.
    * apply is_fresh.
    * set_solver.  
  + exists c; split.
    * unfold support in *; subst a' b'; simpl in *; set_solver.
    * simpl. destruct lamFCB as [d [Hd1 Hd2]].
      specialize (Hd2 [d](⟨ d, c ⟩ • (F m (⟨ a, c ⟩ + x)))).
      apply ((fresh_equivariant ⟨d,c⟩ _ _)) in Hd2; rewrite perm_swap_left in Hd2.
      assert (HH: (⟨ d, c ⟩ • flam [d](⟨ d, c ⟩ • F m (⟨ a, c ⟩ + x))) ≡ flam [c](F m (⟨ a, c ⟩ + x))). {
        rewrite fun_1, nabs_action, name_action_left, (fresh_fixpoint _ _ flam).
        + apply fun_eq; unfold equiv, name_abstraction_equiv; apply alpha_inv_iff; left;
          split; auto. rewrite perm_action_duplicate; reflexivity.
        + apply support_fresh; assumption.
        + repeat apply not_elem_of_union in Hc as [Hc ?]; apply support_fresh; assumption.
      }
      rewrite <-HH; apply Hd2.
  + split; apply support_fresh; subst a'; unfold support in *; simpl in *.
  * apply is_fresh.
  * set_solver.  
Defined.

Print perm_rect_iterator_supported_abstraction.