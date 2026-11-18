Inductive day : Type :=
 | monday
 | tuesday
 | wednesday
 | thrusday
 | friday
 | saturday
 | sunday.

Definition next_weekday (d:day): day :=
 match d with 
 | monday => tuesday
 | tuesday => wednesday
 | wednesday => thrusday
 | thrusday => friday
 | friday => monday
 | saturday => monday
 | sunday => monday
 end.

Example test_next_weekday:
    (next_weekday (next_weekday saturday)) = tuesday.

Proof. simpl. reflexivity. Qed.

Inductive bool : Type :=
 | true
 | false.

Definition negB (b: bool): bool :=
 match b with
  | true => false
  | false => true
  end.

Definition andB (b1: bool) (b2: bool): bool :=
 match b1 with
  | true => b2
  | false => false
 end.

Definition orB (b1 b2: bool) : bool :=
 match b1 with
  | true => true
  | false => b2
  end.

Example test_orb1: (orB true false) = true.

Proof. simpl. reflexivity. Qed.

Example test_orb2: (orB false false) = false.
Proof. simpl. reflexivity. Qed.

Example test_orb3: (orB false true) = true.
Proof. simpl. reflexivity. Qed.

Notation "x && y" := (andB x y).
Notation "x || y" := (orB x y).

Example test_notation1 : (false || false || true) = true.
Proof. simpl. reflexivity. Qed.

Definition negation (b : bool) : bool :=
  if b then false
  else true.

Definition andOperation (b b': bool) : bool :=
  if b then b'
  else false.

Definition nand (b b': bool): bool :=
  (negation (andOperation b b')).

Example test_nand : (nand true true) = false.
Proof. simpl. reflexivity. Qed.

Check true.

Check true : bool.

Check negation.

Inductive rgb: Type :=
 | red
 | green
 | blue.

Module NaturalNumbers.

Inductive nat : Type :=
 | O
 | S (n: nat).

End NaturalNumbers.

Check S 4.

Theorem comutativity_of_and_operator: 
 forall p q : bool, andB p q = andB q p.
Proof.
 intros p q.
 destruct p eqn:Ep.
 - destruct q eqn:Eq.
    + simpl.
      reflexivity.
    + simpl.
      reflexivity.
 - destruct q eqn:Eq.
    + simpl.
      reflexivity.
    + simpl.
      reflexivity.
Qed.