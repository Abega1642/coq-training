Require Import Arith.

Inductive nat_list : Type :=
 | nil
 | cons (n : nat) (l : nat_list).

Notation "x :: l" := (cons x l)  ( at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Definition test_nat_list := 1 :: [].
Definition test_nat_list_2 := [1; 2].

Fixpoint repeat_n (n k : nat) : nat_list :=
 match k with 
  | O => []
  | S k' => n :: ( repeat_n n k' )
 end.

Fixpoint length_of_list (lst : nat_list) : nat :=
 match lst with 
  | [] => 0
  | _ :: tail => S ( length_of_list tail)
 end.


Fixpoint append_list (l_1 l_2 : nat_list) : nat_list :=
 match l_1 with
  | [] => l_2
  | head :: tail => head :: (append_list tail l_2)
 end.


Notation "x ++ y" := (append_list x y).

Theorem list_append_is_associative:
 forall l_1 l_2 l_3 : nat_list, (l_1 ++ l_2) ++ l_3 = l_1 ++ (l_2 ++ l_3).
Proof.
 intros l_1 l_2 l_3.
 induction l_1 as [| h t H].
 - simpl.
   reflexivity.
- simpl.
  rewrite H.
  reflexivity.
Qed.

Fixpoint reverse_list (lst : nat_list) : nat_list :=
 match lst with
  | [] => []
  | h :: t => reverse_list t ++ [ h ]
 end.


Theorem length_of_list_is_distributive:
 forall l_1 l_2 : nat_list, 
  length_of_list (l_1 ++ l_2) = (length_of_list l_1) + (length_of_list l_2).
Proof.
 intros l_1 l_2.
 induction l_1 as [| h t H].
 - simpl.
   reflexivity.
 - simpl.
   rewrite <- H.
   reflexivity.
Qed.    


Theorem reverse_list_has_same_length_as_the_original_list:
 forall lst : nat_list, 
   length_of_list ( reverse_list lst) = length_of_list lst.
Proof.
 intros lst.
 induction lst as [| h t H].
 - simpl.
   reflexivity.
 - simpl.
   rewrite length_of_list_is_distributive.
   simpl.
   rewrite H.
   rewrite Nat.add_1_r.
   reflexivity.
Qed.
Check nil.