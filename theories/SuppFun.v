From Nominal Require Import ProperFun Nominal.

Section SupportedFunctions.
  Context (X Y: Type) `{Nominal X, Nominal Y}.

  Record FunSupp: Type := mkFunSupp {
    (* fsp_from :> Nominal X;
    fsp_to :> Nominal Y; *)
    fsp :> X →ₚ Y;
    fsupp: nameset; (* Function support *)  
    fsupp_spec: ∀ (a b: name), a ∉ fsupp → b ∉ fsupp → 
        ∀ (x: X), (⟨a,b⟩ • (fsp (⟨a,b⟩ • x))) ≡@{Y} fsp x 
  }.
End SupportedFunctions.

Arguments mkFunSupp {_ _ _ _ _ _} _ _ {_}.
Arguments fsp {_ _ _ _ _ _} _.
Arguments fsupp {_ _ _ _ _ _} _.

Notation "'λₛ' x .. y , t" :=
  (@mkFunProper _ _ _ _ _ _ (λ x, .. (@mkFunProper _ _ _ _ _ _ (λ y, t) _ _) ..) _ _)
  (at level 200, x binder, y binder, right associativity).

Notation " A '→ₛ' B " := (FunSupp A B) (at level 99, B at level 200, right associativity).

Print Listset.

Search (list _ -> listset _).

Section FunSuppProperties.
    Context `{Nominal X, Nominal Y}.

    #[global, refine] Instance fsupp_action: PermAct (X →ₛ Y) :=
        λ p fs, mkFunSupp (fun_proper_act p (fsp fs)) _.
    Proof.
      - exact ((fsupp fs) ∪ (Listset (names p))).
      - admit.
    Admitted. 
        
    #[global] Instance fun_support: Support (X →ₛ Y) := λ fs, fsupp fs.
    (* #[global] Instance fsupp_nominal: Nominal (X →ₛ Y). *)
End FunSuppProperties.

Check fun_support.
