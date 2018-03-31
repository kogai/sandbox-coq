Theorem prop0 : forall(A: Prop), A -> A.
Proof.
intros.
apply H.
Qed.

Goal forall (P Q : Prop),
     (forall P : Prop, (P -> Q) -> Q) -> ((P -> Q) -> P) ->  P.
Proof.
intros.
apply H0.
intro.
apply (H (P -> Q)).
apply (H P).
Qed.

(*問2.*)

Theorem p : forall (P Q R : Prop), (P -> Q) -> (Q -> R) -> P -> R.
Proof.
intro.
intro.
intro.
intro.
intro.
intro.
apply H0.
apply H.
apply H1.
Qed.

Inductive list (A: Type) : Type :=
  | nil : list A
  | cons : A -> list A -> list A.

Inductive F : Prop := .
Definition not(A: Prop) := A -> F.

Goal forall P : Prop, P -> ~~P.
Proof.
intros.
intro.
apply H0.
apply H.
Qed.

Goal forall (P Q : Prop), P \/ Q -> Q \/ P.
Proof.
intros.
case H.
 apply or_intror.
 apply or_introl.
Qed.

Goal forall (P Q : Prop), P /\ Q -> Q /\ P.
Proof.
intros.
destruct H.
apply conj.
apply H0.
apply H.
Qed.

Goal forall (P : Prop), P -> ~~P.
Proof.
auto.
Qed.


Theorem q3 : forall (P : Prop), ~(P /\ ~P).
Proof.
intros.
intro.
destruct H.
apply H0.
apply H.
Qed.

Theorem q4 : forall (P Q : Prop), ~P \/ ~Q -> ~(P /\ Q).
Proof.
intros.
intro.
destruct H0.
destruct H.
apply H.
apply H0.
apply H.
apply H1.
Qed.

Theorem q5 : forall (P : Prop), (forall (P : Prop), ~~P -> P) -> P \/ ~P.
Proof.
intros.
apply H.
intro.
apply H0.
right.
intro.
apply H0.
left.
apply H1.
Qed.
