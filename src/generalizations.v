Inductive list (T : Type) : Type :=
 | nil
 | cons (x : T) (l : list T).


Fixpoint repeat (T : Type)  (x : T) (count : nat) : list T := 
 match count with
  | O => nil T
  | S count' => cons T x ( repeat T x count')
 end.

Fixpoint repeat' (T: Type) (x : T) (count : nat) : list T :=
 match count with
  | 0 => nil _
  | S count' => cons _ x (repeat' _ x count')
 end.

Theorem both_definition_of_repeat_should_be_equal:
 forall ( T : Type ) ( x : T ) ( n : nat ),
   repeat T x n =  repeat' T x n.
Proof.
  intros T x n.
  destruct n as [| n'] eqn:E.
  - simpl.
    reflexivity.
  - simpl.
    reflexivity.
Qed.

Notation " x :: y " := (cons _ x y) (at level 60, right associativity).
Notation "[ x ; .. ; y ]" := (cons _ x .. (cons _ y (nil _)) ..).
Notation "[ ]" := (nil _) .


Fixpoint append (T : Type) (l_1 : list T) (l_2 : list T) : list T :=
 match l_1 with
  | [] => l_2
  | h :: t => h :: (append T t l_2)
 end.

Notation "x ++ y" := ( append _ x y) (at level 60, right associativity).

Fixpoint length (T : Type) (lst : list T) : nat :=
 match lst with
  | [] => 0
  | h :: t => S ( length T t)
 end.


(**
    These following proofs remind of the fact that Set of list
    is a monoid.
    Recall:
      Let (G, ×) be an algebraic structure.
      - G is not an empty set
      - e \in G is an identity element if and only if :
          forall x \in G, x × e = e × x = x.
      - forall x, y, z \in G, (x × y) × z = x × (y × z)

    (but not every element has an inverse)

    Here :
      - G = Set of all lists of T.
      - × = append, noted "++"
      - e = []

    The proofs below give exactly these properties, so (list T, ++, [])
    is a monoid.
**)

Theorem append_nil_l:
 forall ( T : Type ) ( lst : list T ), [] ++ lst = lst.
Proof.
  intros T lst.
  simpl.
  reflexivity.
Qed.

Theorem append_nil_r:
 forall ( T : Type ) ( lst : list T ), lst ++ [] = lst.
Proof.
 intros T lst.
 induction lst as [| h t H].
 - simpl.
   reflexivity.
 - simpl.
   rewrite H.
   reflexivity.
Qed.

Theorem associativity_of_append:
 forall ( T : Type ) (l_1 l_2 l_3 : list T),
   (l_1 ++ l_2) ++ l_3 = l_1 ++ (l_2 ++ l_3).
Proof.
  intros T l_1 l_2 l_3.
  induction l_1 as [| h t H].
  - simpl.
    reflexivity.
  - simpl.
    rewrite H.
    reflexivity.
Qed.

(**
    These following proofs remind of the definition of Monoid homomorphism.
    Recall:
        Let (G_1, ++, e_1) and (G_2, +, e_2) be two monoids.
        Let f be a homomorphism from G_1 to G_2 such that:
         f:  G_1 -> G_2
             x_1 |-> f(x_1)
        - forall x_1, x_2 \in G_1, we have : f(x_1 ++ x_2) = f(x_1) + f(x_2)
        - f( e_1 ) = e_2
        (where e_1 \in G_1 and e_2 \in G_2 are their respective identity)

    But here we have :
      -  (G_1 , ++, e_1) := ( {list of a type T}, append, [] ), append is noted as "++"
      -  (G_2 , +, e_2)  := ( nat , + , 0 )
      -  f  := length of a type T.

    length_preserves_operations_over_nat is the first condition and
    length_preserves_identity_over_nat is the second one, so length is
    indeed a monoid homomorphism from (list T, ++, []) to (nat, +, 0).
**)

Theorem length_preserves_operations_over_nat:
 forall ( T : Type ) ( l_1 : list T ) ( l_2 : list T ),
   length T ( l_1 ++ l_2 ) = length T l_1 + length T l_2.
Proof.
 intros T l_1 l_2.
 induction l_1 as [| h t H].
 - simpl.
   reflexivity.
 - simpl.
   rewrite <- H.
   reflexivity.
Qed.

Lemma length_preserves_identity_over_nat:
 forall ( T : Type ), length T [] = 0.
Proof.
 intros T.
 simpl.
 reflexivity.
Qed.

Inductive couple (X Y : Type) : Type :=
 | pair (x : X) (y : Y).

Notation "( x , y )" := ( pair _ _ x y).


Fixpoint combine ( X Y : Type ) (l_x : list X) (l_y : list Y) : list ( couple X Y ) :=
 match l_x, l_y with
  | [], _ => []
  | _, [] => []
  | (h_x :: t_x) , (h_y :: t_y) => ( (h_x, h_y ) :: ( combine X Y t_x t_y))
 end.

Example map_of_bool_and_nat:
 ( combine nat bool [0; 1] [false; true] ) = [ (0 , false); (1 , true)].
Proof.
 simpl.
 reflexivity.
Qed.