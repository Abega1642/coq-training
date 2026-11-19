Inductive nat_prod: Type :=
 | pair (n m : nat).

Check (pair  2 3).

Definition first (prd : nat_prod) : nat :=
 match prd with
  | pair x _ => x
 end.

Definition second (prd : nat_prod) : nat :=
 match prd with
  | pair _ y => y
 end.

Compute first (pair 2 3).
Compute second (pair 2 3).


Notation "( x , y )" := (pair x y).

Check ( 2 , 3 ).

Compute first ( 3 , 2 ).
Compute second ( 3, 2 ).

Definition first' (prd : nat_prod) : nat :=
 match prd with 
  | ( x , _) => x
 end.

Definition second' (prd : nat_prod) : nat :=
 match prd with
  | ( _ , y ) => y
 end.

Theorem surjective_pairing :
 forall n m : nat, (n, m) = (first (n, m), second (n, m)).
Proof.
 intros n m.
 simpl.
 reflexivity.
Qed.

Theorem surjective_pairing_general :
 forall p : nat_prod, p = (first p, second p).
Proof.
 intros p.
 destruct p as [n m].
 apply surjective_pairing.
Qed.
