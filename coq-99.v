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
