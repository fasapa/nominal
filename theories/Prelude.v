From stdpp Require Export prelude.

(* Essêncial para o mecânismo de busca de provas não entrar em loop.
   Coq sempre vai buscar, pelo menos uma instância, de uma classe ao relizar
   alguma "operação". Por estarmos trabalhando com setoids todas nossas
   classes definiem uma dependência da classe Equiv. Ao utilizar uma classe (C w)
   que, ainda, não possui uma instância Equiv w, Coq busca por instâncias existentes,
   que na maioria dos casos é tt. Entretanto não existe uma instância para C tt, 
   pois ele encontrou Equiv tt, mas como não existe C tt, ele faz backtrack e
   pega a próxima opção: Equiv (list A). O ciclo se repete: existe Equiv (list tt)
   mas não existe C (list tt)), existe Equiv (list (list tt)), mas não existe 
   C (list (list tt))... Para impedir isso adicionamos o modo abaixo. A opção ! 
   diz que o (a caberça) do argumento A de Equiv A é utilizado como entrada no 
   algoritmo de unifição, e não saida. Dessa forma A guia a unificação, e não
   uma resposta a ser encontrada.

https://coq.inria.fr/refman/proofs/automatic-tactics/auto.html#coq:cmd.Hint-Mode *)
#[global] Hint Mode Equiv ! : typeclass_instances.

Notation " R ⟹ R' " := (@respectful _ _ (R%signature) (R'%signature))
    (right associativity, at level 55) : signature_scope.

Declare Scope nominal_scope.
Delimit Scope nominal_scope with nom.
Open Scope nominal_scope.