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

Definition FCB `{Nominal X, Nominal Y} (f: X →ₛ Y): Prop :=
  ∃ (a: Name), a ∉ (support f) ∧ (∀ x: X, a # (f x)).
 
Theorem freshness `{Nominal X} (h: Name →ₛ X): 
  ∃ (a: Name), a #[h, (h a)]. Admitted.

(* Definition perm_rect_1_general := fun (P : Term → Type)
  (fvar : ∀ a : Name, P (Var a))
  (fapp : ∀ m: Term, P m → ∀ n: Term, P n → P (App m n))
  (flam : ∀ a : Name, ∀ m: Term, P m → P (Lam (a,m))) =>
  fix F (t: Term) : Perm → P t :=
    match t as t' return (Perm → P t') with
    | Var a => fun p => fvar (p • a)
    | App m n => fun p => fapp m (F (p • m) p) n (F (p • n) p)
    | Lam (a, m) => fun p => flam a m (F (p • m) p)
    end. *)

(* Lemma perm_rect_dependent_general (P : Term → Type)
  (fvar : ∀ a : Name, P (Var a))
  (fapp : ∀ m: Term, P m → ∀ n: Term, P n → P (App m n))
  (flam : ∀ a : Name, ∀ m: Term, P m → P (Lam (a,m))) :
  ∀ t, Perm → P t.
Proof.
  intros t; apply (term_rect_general (fun t: Term => Perm → P t)).
  - intros a p; exact (fvar (p • a)).
  - intros m Fm n Fn p; exact (fapp m (Fm p) n (Fn p)).
  - intros a m Fm p; exact (flam a m (Fm p)).
Defined. *)

(* Definition perm_rect_nominal_image_general `{Nominal X}
  (fvar: Name → X)
  (fapp: Term → X → Term → X → X)
  (flam: Name → Term → X → X) 
  : Term → Perm → X :=
  perm_rect_dependent_general (fun _: Term => X) fvar fapp flam. *)

(* Definition term_rect_iterator {X: Type} := fun
  (fvar : Name → X)
  (fapp : X → X → X)
  (flam : Name → X → X) =>
fix F (t: Term) : X :=
  match t as t' return X with
  | Var a => fvar a
  | App t1 t2 => fapp (F t1) (F t2)
  | Lam (a, t) => flam a (F t)
  end. *)

(* Definition term_rect_iterator_from_general {X: Type}
  (fvar : Name → X)
  (fapp : X → X → X)
  (flam : Name → X → X) : Term → X := fun t =>
  term_rect_general (fun _ => X)
    fvar 
    (fun _ Fm _ Fn => fapp Fm Fn)
    (fun a _ Fm => flam a Fm)
    t. *)

(* Definition term_rect_general_nondependent `{Nominal X}
  (fvar : Name → X)
  (fapp : Term → X → Term → X → X)
  (flam : Name → Term → X → X) : Term → X :=
  term_rect_general (fun _ => X) fvar fapp flam. *)

(* Definition term_rect_iterator_supported `{Nominal X} := fun
  (fvar : Name →ₛ X)
  (fapp : (X * X) →ₛ X)
  (flam : (Name * X) →ₛ X) =>
fix F (t: Term) : X :=
  match t as t' return X with
  | Var a => fvar a
  | App t1 t2 => fapp ((F t1), (F t2))
  | Lam (a, t) => flam (a, (F t))
  end. *)

(* Lemma fun_equivar `{PermT X, PermT Y} (p : Perm) (f: X → Y):
  p • f ≡ f ↔ ∀ x, p • (f x) ≡ f(p • x).
Proof. Admitted. *)

(* Lemma equivar2 {X: Type} `{Nominal Y, Nominal Z} (p : Perm) (f: X → (Y →ₛ Z)) (x: X) (y : Y):
  p • (f x y) ≡ f x (p • y).
Proof.
  pose proof (equivar (X := Y) (Y := Z)).
  specialize (H3 p (f x) y). apply H3.
Qed. *)


Lemma fun_1 `{Nominal X, Nominal Y} (p : Perm) (f: X →ₛ Y) (x : X):
  p • (f x) ≡ (p • f)(p • x).
Proof.
  unfold action at 2; unfold fun_supp_act; simpl. 
  rewrite perm_left_inv; reflexivity.
Qed.

Definition perm_rect_iterator_supported `{Nominal X} (A : NameSet)
  (fvar : Name →ₛ X)
  (fapp : (X * X) →ₛ X)
  (flam : (Name * X) →ₛ X) : Term → (Perm →ₛ X).
Proof.
  refine(
    fix F (t: Term) :=
      match t with
      | Var a => 
        λₛ⟦ support fvar ∪ support a ⟧ p, fvar (p • a)
      | App t1 t2 => 
        λₛ⟦ support fapp ∪ support (F t1) ∪ support (F t2) ⟧ p, fapp ((F t1) p, (F t2) p)
      | Lam (a, t) => 
        λₛ⟦ support flam ∪ support (F t) ∪ support a ⟧ p, flam (a, (F t p))
      end
  ).
  - repeat intro; rewrite H1; reflexivity.
  - intros w z Hw Hz p. unfold action at 3. unfold perm_action.
    rewrite <-2!gact_compat, <-perm_inv, (fresh_fixpoint _ _ a).
      + rewrite perm_inv at 2; rewrite <-fsupp_action, fresh_fixpoint.
        * reflexivity.
        * admit.
        * admit.       
      + apply support_fresh; unfold support, name_support. admit.
      + apply support_fresh; unfold support, name_support. admit.
  - repeat intro; rewrite H1; reflexivity.
  - intros w z Hw Hz p.
    rewrite <-(fresh_fixpoint w z (F t1)) at 1; try (apply support_fresh; admit).
    rewrite <-(fresh_fixpoint w z (F t2)) at 1; try (apply support_fresh; admit).
    rewrite <-2!fun_1, <-prod_act; rewrite perm_inv at 2; rewrite <-fsupp_action.
    rewrite fresh_fixpoint; try (apply support_fresh; admit); reflexivity.
  - repeat intro; rewrite H1; reflexivity.
  - clear p t0; intros w z Hw Hz p.
    rewrite <-(fresh_fixpoint w z (F t)) at 1; try (apply support_fresh; admit).
    rewrite <-(fresh_fixpoint w z a) at 1; try (apply support_fresh; admit).
    rewrite <-fun_1, <-prod_act; rewrite perm_inv at 2; rewrite <-fsupp_action.
    rewrite fresh_fixpoint; try (apply support_fresh; admit); reflexivity.
Admitted.

Check perm_rect_iterator_supported.