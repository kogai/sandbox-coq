Require Import Arith.
Require Import List.

(*
Fixpoint ack (n m : nat) : nat :=
  match n with
    | O => S m
    | S n' =>
    match m with
      | O => ack n' 1
      | S m' => ack n' (ack n m')
    end
  end.
*)
  
(* ack n' = f *)
Fixpoint ack' (f : nat -> nat)(m : nat) : nat :=
  match m with
    | O => f 1
    | S m' => f (ack' f m')
  end.
  
Fixpoint ack (n m : nat): nat :=
  match n with
    | O => S m
    | S n' => ack' (ack n') m
  end.
  
Fixpoint split (l : list nat) : list nat * list nat :=
  match l with
    | nil => (nil, nil)
    | x::nil => (x::nil, nil)
    | x::y::zs => (fun l' => (x::fst l', y::snd l')) (split zs)
  end.
  
