Require Import Arith.

Goal forall (n m : nat),  n = m \/ n <> m.
Proof.
  induction n.
    destruct m.
      left.
      reflexivity.
      right.
      discriminate.
    
    intro.
    destruct m.
      right.
      discriminate.
      
      destruct (IHn m).
        left.
        f_equal.
        apply H.
        right.
        apply not_eq_S.
        apply H.
Qed.