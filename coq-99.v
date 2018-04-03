Goal forall (P Q : Prop), (P -> Q) -> P -> Q.
  intros.
  apply H.
  apply H0.
Qed.

Lemma Coq_01 : forall A B C:Prop, (A->B->C) -> (A->B) -> A -> C.
intros.
apply H.
apply H1.
apply H0.
apply H1.
Qed.

Lemma Coq_02 : forall A B C:Prop, A /\ (B /\ C) -> (A /\ B) /\ C.
intros.
split.
destruct H.
destruct H0.
split.
apply H.
apply H0.
destruct H.
destruct H0.
apply H1.
Qed.

Lemma Coq_03 : forall A B C D:Prop, (A -> C) /\ (B -> D) /\ A /\ B -> C /\ D.
intros.
destruct H.
destruct H0.
destruct H1.
split.
apply H.
apply H1.
apply H0.
apply H2.
Qed.

Lemma Coq_04 : forall A : Prop, ~(A /\ ~A).
intros.
intro.
destruct H.
apply H0.
apply H.
Qed.

Lemma Coq_05 : forall A B C:Prop, A \/ (B \/ C) -> (A \/ B) \/ C.
intros.
destruct H.
left.
left.
apply H.
destruct H.
left.
right.
apply H.
right.
apply H.
Qed.

Lemma Coq_06 : forall A, ~~~A -> ~A.
intros.
intro.
apply H.
intro.
apply H1.
apply H0.
Qed.

Lemma Coq_07 : forall A B:Prop, (A->B)->~B->~A.
intros.
intro.
apply H0.
apply H.
apply H1.
Qed.

Lemma Coq_08: forall A B:Prop, ((((A->B)->A)->A)->B)->B.
intros.
apply H.
intros.
apply H0.
intros.
apply H.
intros.
apply H1.
Qed.

Lemma Coq_09 : forall A:Prop, ~~(A\/~A).
intros.
intro.
apply H.
right.
intro.
apply H.
left.
apply H0.
Qed.


