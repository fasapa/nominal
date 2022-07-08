From stdpp Require Export list.
From Nominal Require Import Swap.

(* Permutation is just a list of pair of names. *)
Notation perm := (list (name * name)).

Definition perm_swap (p: perm): name → name := 
  λ a, foldl (λ x y, swap y x) a p.

(* Properties *)
Lemma perm_swap_app (r s: perm) a: perm_swap (r ++ s) a = perm_swap s (perm_swap r a).
Proof. unfold perm_swap; rewrite foldl_app; simpl; auto. Qed.

Lemma perm_swap_left_rev (p: perm): ∀ a, perm_swap (reverse p) (perm_swap p a) = a.
Proof with auto.
  assert (HH: ∀ {A} (x: A) y, x :: y = [x] ++ y)... induction p; intros.
  - simpl...
  - rewrite HH, reverse_app, reverse_singleton, <-perm_swap_app, <-app_assoc,
      3?perm_swap_app; simpl; rewrite IHp; apply swap_involutive.
Qed.

Lemma perm_swap_right_rev (p : perm) a: perm_swap p (perm_swap (reverse p) a) = a.
Proof with auto.
  assert (HH: ∀ {A} (x: A) y, x :: y = [x] ++ y)... induction p.
  - simpl...
  - rewrite HH, reverse_app, reverse_singleton, <- perm_swap_app, <-app_assoc, 
      3?perm_swap_app; simpl; rewrite swap_involutive...
Qed.

Lemma perm_swap_neither (a b c: name): a ≠ b → a ≠ c → perm_swap ⟨b,c⟩ a = a.
Proof. unfold perm_swap, foldl; intros; rewrite swap_neither1; intuition. Qed.

Lemma perm_swap_left (a b: name): perm_swap ⟨a,b⟩ a = b.
Proof. unfold perm_swap, foldl; apply swap_left. Qed.

Lemma perm_swap_right (a b: name): perm_swap ⟨b,a⟩ a = b.
Proof. unfold perm_swap, foldl. apply swap_right. Qed.

Lemma perm_swap_neq p: ∀ a b, a ≠ b → perm_swap p a ≠ perm_swap p b.
Proof. induction p as [|[] ? IHp]; [| intros; simpl; apply IHp,swap_neq]; auto. Qed.

(* Permutation domain *)
Fixpoint perm_dom (p: perm): nameset :=  
  match p with
  | [] => ∅
  | (a,b) :: p' => {[a; b]} ∪ perm_dom p'
  end.

(* Proof depends on listset_empty implementation. TODO: alternative? *)
Lemma perm_dom_concat p: ∀ p', perm_dom (p ++ p') = (perm_dom p) ∪ (perm_dom p').
Proof.
Transparent listset_empty.
  induction p.
  - intros; simpl; unfold empty, listset_empty, union, listset_union; simpl;
      destruct (perm_dom p'); reflexivity.
  - intros; simpl; destruct a as [a b]; rewrite IHp, assoc; auto.
    unfold Assoc, union, listset_union; intros [] [] []; rewrite assoc; [auto | typeclasses eauto].
Opaque listset_empty.
Qed.

Lemma perm_notin_domain_id (p: perm) (a: name): a ∉ (perm_dom p) → perm_swap p a = a.
Proof.
  intros; induction p as [| [b c] p'].
  - reflexivity.
  - assert (HH: ∀ A (x: A) y, x :: y = [x] ++ y). { reflexivity. }
    rewrite HH, perm_swap_app; simpl in H; do 2 apply not_elem_of_union in H as [H ?];
    rewrite perm_swap_neither; set_solver.
Qed.