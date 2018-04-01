Require Import Arith.
Require Import List.

Goal forall (P Q R S : Prop), (S /\ P) /\ (Q /\ R) -> (P /\ S) /\ (R /\ Q).
Proof.
intros.
destruct H.
assert(forall(X Y : Prop), X /\ Y -> Y /\ X).
intros.
destruct H1.
split.
apply H2.
apply H1.
split.
apply H1.
apply H.
apply H1.
apply H0.
Qed.


Theorem app_eq_nil : forall (A : Type)(l l':list A), l ++ l' = nil -> l = nil /\ l' = nil.
Proof.
intros.
split.
destruct l.
  reflexivity.
  discriminate.
destruct l'.
  reflexivity.
  destruct l.
    discriminate.
    discriminate.
Qed.

Goal forall (A : Type)(a : A), nil <> a :: nil.
Proof.
  intros.
  discriminate.
Qed.

Goal forall (n m : nat)(f : nat -> nat), f n = n -> S (f (f n)) = S m -> n = m.
Proof.
  intros.
  congruence.
Qed.

Goal forall (A : Type)(x y : A), x :: y :: nil <> x :: nil.
Proof.
  intros.
  congruence.
Qed.

(*
Goal forall (P Q : nat -> Prop)(a : nat), P (a * 2) \/ Q (a * 2).
Proof.
  intros.
  replace (Q (a * 2)) with (Q (2 * a)).
  simpl.
  
  rewrite mult_comm.
*)

Goal forall (P : nat -> nat -> Prop)(a b c d : nat), P a d -> a = b -> c = d -> P b c.
intros.
subst.
apply H.
Qed.


(*
Lemma removelast_app : forall (A : Type)(l l' : list A), l' <> nil  ->
  removelast (l++l') = l ++ removelast l'.
Proof.
  intros.
  induction l.
    reflexivity.
    simpl.
    remember (l ++ l').
    destruct l0.
      apply False_ind.
      apply H.
      apply (app_eq_nil l l').
*)



Goal forall (n : nat), (exists m, n = 2 * m) \/ (exists m, n = 2 * m + 1).
Proof.
  intros.
  induction n.
    left.
    exists 0.
    simpl.
    reflexivity.
    destruct IHn.
      right.
      destruct H.
      exists x.
      rewrite H.
      rewrite plus_comm.
      reflexivity.
      
      destruct H.
        left.
        exists (S x).
        rewrite plus_comm in H.
        rewrite mult_succ_r.
        rewrite plus_comm.
        rewrite H.
        simpl.
        reflexivity.
Qed.

Inductive InList (A : Type)(a: A): list A -> Prop :=
  | headIL : forall xs, InList A a (a::xs)
  | consIL : forall x xs, InList A a xs -> InList A a (x::xs).

Goal forall (A : Type)(l m : list A) (a : A),
  InList A a (l ++ m) -> InList A a l \/ InList A a m.
Proof.
  intros.
  induction l.
  right.
  apply H.
  
  inversion H.
    subst.
    left.
    constructor.
    
    destruct (IHl H1).
      left.
      constructor.
      apply H3.
      right.
      apply H3.
Qed.
