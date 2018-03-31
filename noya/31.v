(*1*)
Goal forall (A B: Prop), A -> (B -> (and A B)).
Proof.
intros.
apply conj.
apply H.
apply H0.
Qed.

(*2*)
Goal forall(A B : Prop), (A /\ ~(A /\ B)) -> ~B.
Proof.
intros.
destruct H.
intro.
apply H0.
apply conj.
apply H.
apply H1.
Qed.

(*3*)
Goal forall (A B C : Prop), (A -> (B /\ C)) -> ((A -> B) /\ (A -> C)).
Proof.
intros.
apply conj.
intros.
case H.
apply H0.
intros.
apply H1.
intros.
destruct H.
apply H0.
apply H1.
Qed.

(*4*)
Goal forall (A B : Prop), ((A \/ B) /\ (A -> B)) -> B.
Proof.
intros.
destruct H.
case H.
apply H0.
intros.
apply H1.
Qed.

(*5*)
Goal forall (A B C : Prop), (A -> B) -> ((C \/ A) ->  (C \/ B)).
Proof.
intros.
destruct H0.
left.
apply H0.
right.
apply H.
apply H0.
Qed.


