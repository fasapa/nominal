From stdpp Require Import list.
Require Export Name.

Open Scope nominal_scope.

(** *Permutação é decomposta em permutações de 2-ciclo, chamado de  transposinção/swap. *)
Definition swap: Set := prod name name.
Global Instance swap_inhabited: Inhabited swap :=
  populate (inhabitant, inhabitant).

(* Must remove duplicates *)
(* Global Instance swap_elements : Elements name swap := λ '(a,b), [a;b]. *)

(** *Dessa forma permutação é representado como uma lista de transposições *)
Definition perm: Set := list swap.
Global Instance perm_inhabited : Inhabited perm := populate [].

(* Global Instance perm_elements : Elements name perm := *)

(** *Ação de permutação sobre o tipo A *)
Class Action A := act: perm -> A -> A.
Global Hint Mode Action ! : typeclasses_instances.
Instance: Params (@act) 2 := {}.

Infix "∙" := act (at level 60, right associativity) : nominal_scope.
(* Notation "∙@{ A }" := (@act A _) (only parsing). *)
Notation "(∙)" := act (only parsing) : nominal_scope.
Notation "( x ∙)" := (act x) (only parsing) : nominal_scope.
Notation "(∙ x )" := (λ y, act y x) (only parsing) : nominal_scope.

(** *Ação de permutação sobre o conjunto de nomes  *)
Global Instance name_action: Action name := λ p a,
 let s := (λ '(x,y) b, if decide (x = b) then y else
                         if decide (y = b) then x else b)
 in foldr s a p.

(** *Equivalência de permutação
    A ação (a a) ∙ p é equivalente á [] ∙ p, portanto precisamos de uma
    relação de equivalência intensional. *)
Global Instance perm_equiv : Equiv perm :=
  λ p q : perm, forall a : name, p ∙ a = q ∙ a.

Global Instance perm_equivalence : Equivalence (≡@{perm}).
Proof. repeat split; repeat intro; [symmetry | etransitivity]; eauto. Qed.

Infix "+" := app : nominal_scope.
Notation "(+)" := app (only parsing) : nominal_scope.
Notation "( x +)" := (app x) (only parsing) : nominal_scope.
Notation "(+ x )" := (λ y, app y x) (only parsing) : nominal_scope.
Notation "- x" := (reverse x) : nominal_scope.
Notation "(-)" := reverse (only parsing) : nominal_scope.
Notation "x - y" := (x + (-y))%nominal : nominal_scope.

(* Permutação identidade *)
Notation ι := (@nil swap).

(* Tipo de permutação possui uma noção de ação de permutação. *)
Class Perm A `{Action A} : Prop := {
  (* stdpp LeftId defined for homoge operator *)
  act_id (x : A) : ι ∙ x = x;
  act_compat (p q: perm) (x : A) : (p + q) ∙ x = p ∙ (q ∙ x);
  act_proper :> Proper ((≡@{perm}) ==> (=@{A}) ==> (=@{A})) (∙)
}.

(* Nomes são um tipo de permutação com a ação name_action *)
Global Instance name_perm : Perm name.
Proof.
  repeat split; repeat intro;
    [unfold act, name_action; rewrite foldr_app |
     match goal with H : _ = _ |- _ => rewrite H end]; auto.
Qed.

(** *Permutação forma um grupo aditivo com a equivalência perm_equiv *)

Lemma swap_involutive (a: swap): [a] + [a] ≡ ι.
Proof.
  destruct a; unfold equiv, perm_equiv, act, name_action; intros x;
    simpl; repeat case_decide; congruence.
Qed.

Lemma identity_neq_eq: ι = -ι. Proof. auto. Qed.

(* Propriedades de tipos de permutação *)
Lemma perm_action_left_inv_eq `{Perm A} (p : perm) (x: A): (-p + p) ∙ x = x.
Proof.
  induction p; simpl; [apply act_id | idtac];
    assert (HH: a :: p = [a] ++ p). auto.
  rewrite reverse_cons, HH, <-app_assoc, act_compat, app_assoc, act_compat,
  swap_involutive, act_id, <-act_compat; auto.
Qed.

Lemma perm_action_right_inv_eq `{Perm A} (p: perm): forall (x: A), (p ++ (-p)) ∙ x = x.
Proof.
  induction p; simpl; intros; [apply act_id | idtac];
    assert (HH: forall {A: Type} (a: A) l, a :: l = [a] ++ l). auto.
  rewrite reverse_cons, HH, act_compat, app_assoc, act_compat, IHp,
  <-act_compat, swap_involutive; apply act_id.
Qed.

Lemma action_left_inv_eq `{Perm A} (p: perm) (x: A) : (-p) ∙ p ∙ x = x.
Proof. rewrite <-act_compat, perm_action_left_inv_eq; auto. Qed.

Lemma action_right_inv_eq `{Perm A} (p: perm) (x: A) : p ∙ (-p) ∙ x = x.
Proof. rewrite <-act_compat, perm_action_right_inv_eq; auto. Qed.

Lemma perm_iff `{Perm A} (p: perm) (x y: A): p ∙ x = y <-> x = (-p) ∙ y.
Proof.
  split; intros HP; [symmetry; rewrite <-HP | rewrite ->HP];
    [apply action_left_inv_eq | apply action_right_inv_eq].
Qed.

Lemma perm_inj `{Perm A} (p: perm) (x y: A): p ∙ x = p ∙ y -> x = y.
Proof.
  intros HP; apply perm_iff in HP; rewrite HP; apply action_left_inv_eq.
Qed.

(* Axiomas de grupo *)
Lemma perm_left_id (p: perm): ι + p ≡ p.
Proof. auto. Qed.

Lemma perm_right_id (p: perm): p + ι ≡ p.
Proof. rewrite app_nil_r; auto. Qed.

Lemma perm_assoc (p q r: perm): (p + q) + r ≡ p + (q + r).
Proof. rewrite app_assoc; auto. Qed.

Lemma perm_left_inv (p: perm): (-p) + p ≡ ι.
Proof.
  unfold equiv, perm_equiv; intros; rewrite act_id;
    apply perm_action_left_inv_eq.
Qed.

Lemma perm_right_inv (p: perm): p + (-p) ≡ ι.
Proof.
  unfold equiv, perm_equiv; intros; rewrite act_id;
    apply perm_action_right_inv_eq.
Qed.

Lemma perm_equiv_impl_inv (p q: perm): p ≡ q -> (-p) ≡ (-q).
Proof.
  unfold equiv, perm_equiv; intros H x; transitivity ((-q) ∙ p ∙ (-p) ∙ x);
    [rewrite H, action_left_inv_eq | rewrite action_right_inv_eq]; auto.
Qed.

(** *Outras tipos de permutação *)

(* List *)
Global Instance list_action `{Action A}: Action (list A) :=
  λ p l, map (p ∙) l.
Global Instance perm_list `{Perm A}: Perm (list A).
Proof with auto.
  repeat split.
  - intros l; induction l as [| ? ? IHl]...
    unfold act, list_action in *; rewrite map_cons, IHl, act_id...
  - intros ? ? l; unfold act, list_action; rewrite map_map;
      induction l as [| ? ? IHl]...
    rewrite map_cons, map_cons, IHl; f_equal; apply act_compat.
  - repeat intro;
      match goal with
        H: _ = ?l |- _ => rewrite H; clear H; induction l as [| ? ? IHl]
      end...
    unfold act, list_action in *; do 2 rewrite map_cons; f_equal...
    apply act_proper...
Qed.

(* Prod *)
Global Instance prod_action `{Action A, Action B}: Action (A * B) :=
  λ p prd, prod_map (@act A _ p) (@act B _ p) prd.
Global Instance perm_prod `{Perm A, Perm B}: Perm (A * B).
Proof with auto.
  repeat split.
  - intros []; unfold act, prod_action; simpl; do 2 rewrite act_id...
  - intros ? ? []; unfold act, prod_action; simpl; do 2 rewrite act_compat...
  - intros ? ? HHH [] [] HH; rewrite HH; unfold act, prod_action; simpl;
      rewrite HHH...
Qed.

(* Functions *)
Global Instance fun_action `{Action A, Action B}: Action (A -> B) :=
  λ p f x, p ∙ (f (-p ∙ x)).

Global Instance fun_perm `{Perm A, Perm B}: Perm (A -> B).
Proof.
  repeat split.
  - intros f. unfold act, fun_action.
    Unset Printing Notations. setoid_rewrite act_id.
    setoid_rewrite act_id.
