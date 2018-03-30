Definition plus (n : nat)(m : nat) : nat := n + m.
Definition plus': nat -> nat -> nat := fun n m => n + m.
Definition id (A: Type)(x: A): A := x.
Definition id' : forall (A: Type), A -> A := fun A x => x.
Definition prop0 : forall (A: Prop), A -> A := fun A x => x.

Definition prop1 : forall (A B C : Prop), (B -> C) -> (A -> B) -> A -> C
  := fun A B C f g x => f (g x).

(* 問0. 任意の命題 A B に対して、A ならば 「A ならば B」ならば Bが成り立つ。 *)

Definition q0 : forall (A B : Prop), A -> (A -> B) -> B
  := fun A B a f => f a.

(*問1. 任意の命題 A B C に対して、「A ならば B ならば C」ならば「B ならば A ならば C」が成り立つ*)
Definition q1 : forall (A B C : Prop), (A -> B -> C) -> (B -> A -> C)
  := fun A B C f b a => f a b.