Inductive bool : Type :=
  | true
  | false.

Definition negb (b:bool) : bool :=
  match b with
  | false => true
  | true => false
  end.

Definition nandb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | false => true
  | true => negb b2
  end.

Example test_nandb1:(nandb true false) = true.
Proof. simpl. reflexivity. Qed.

Example test_nandb2:(nandb false false) = true.
Proof. simpl. reflexivity. Qed.

Definition andb2 (b1:bool)(b2:bool) : bool :=
  match b1 with
  | false => false
  | true => b2
  end.

Notation "x && y" := (andb2 x y).

Definition andb3 (b1:bool)(b2:bool)(b3:bool) : bool :=
  match b1 with
  | false => false
  | true => andb2 b2 b3
  end.

Example test_andb31:(andb3 true true true) = true.
Proof. simpl. reflexivity. Qed.

Example test_andb32:(andb3 false true false) = false.
Proof. simpl. reflexivity. Qed.


Module NatPlayground.

Inductive nat : Type :=
  | O
  | S (n:nat).
End NatPlayground.

Fixpoint evenb (n:nat) : bool :=
  match n with
  | O => true
  | S O => false
  | S (S n') => evenb n'
  end.

Definition oddb (n:nat) : bool := negb (evenb n).

Module NatPlayground2.

Fixpoint plus (n m :nat) : nat :=
  match n with
  | O => m
  | S n' => S (plus n' m)
  end.

Fixpoint mult (n m : nat) : nat :=
  match n with
    | O => O
    | S n' => plus m (mult n' m)
  end.
Fixpoint minus (n m:nat) : nat :=
  match n, m with
  | O , _ => O
  | S _ , O => n
  | S n', S m' => minus n' m'
  end.
End NatPlayground2.
Compute (mult 3 2).

Fixpoint exp (base power : nat) : nat :=
  match power with
    | O => S O
    | S p => mult base (exp base p)
  end.

Notation "x + y" := (plus x y)
                       (at level 50, left associativity)
                       : nat_scope.
Notation "x - y" := (minus x y)
                       (at level 50, left associativity)
                       : nat_scope.
Notation "x * y" := (mult x y)
                       (at level 40, left associativity)
                       : nat_scope.

(*n的阶乘*)
Fixpoint factorial (n:nat) : nat :=
  match n with
  | O => S O
  | S n' => n * (factorial n')
  end.

Example test_factorial1 : (factorial 3) = 6.
Proof. simpl. reflexivity. Qed.

Fixpoint eqb (n m : nat) : bool :=
  match n with
  | O => match m with
         | O => true
         | S m' => false
         end
  | S n' => match m with
            | O => false
            | S m' => eqb n' m'
            end
  end.

Fixpoint leb (n m : nat) : bool :=
  match n with
  | O => true
  | S n' =>
      match m with
      | O => false
      | S m' => leb n' m'
      end
  end.

Fixpoint ltb (n m : nat) : bool :=
  match n with
  | O => match m with
          | S m' => true
          | O => false
          end
  | S n'=> match m with
          | O => false
          | S m' => ltb n' m'
          end
  end.

Notation "x =? y" := (eqb x y) (at level 70) : nat_scope.
Notation "x <=? y" := (leb x y) (at level 70) : nat_scope.
Notation "x <? y" := (ltb x y) (at level 70) : nat_scope.

Example test_ltb1: (ltb 2 2) = false.
Proof. simpl. reflexivity. Qed.

Example test_ltb3: (ltb 4 2) = false.
Proof. simpl. reflexivity. Qed.

Theorem plus_O_n : forall n : nat, 0 + n = n.
Proof.
  intros n. simpl. reflexivity. Qed.


Theorem plus_1_l : forall n:nat, 1 + n = S n.
Proof.
  intros n. reflexivity. Qed.

Theorem mult_0_l : forall n:nat, 0 * n = 0.
Proof.
  intros n. reflexivity. Qed.


Theorem plus_id_example : forall n m :nat,
 n = m -> n + n = m + m.
Proof. intros n m. intros H. rewrite <-H. reflexivity. Qed.

Theorem plus_id_exercise : forall n m o : nat,
  n = m -> m = o -> n + m = m + o.
Proof.
  intros n m o.
  intros H1.
  intros H2.
  rewrite H1, H2.
  reflexivity. Qed.

Theorem mult_0_plus : forall n m : nat,
  (0 + n) * m = n * m.
Proof.
  intros n m.
  rewrite -> plus_O_n.
  reflexivity. Qed.

Theorem mult_S_1 : forall n m : nat,
  m = S n -> m * (1+n) = m*m.
Proof.
  intros n m.
  intros H1.
  rewrite H1.
  reflexivity.
  Qed.

Theorem andb_commutative : forall b c, andb b c = andb c b.
Proof.
  intros b c. destruct b eqn:Eb.
  - destruct c eqn:Ec.
    + reflexivity.
    + reflexivity.
  - destruct c eqn:Ec.
    + reflexivity.
    + reflexivity.
Qed.

Theorem andb3_exchange :
  forall b c d, andb (andb b c) d = andb (andb b d) c.
Proof.
  intros b c d. destruct b eqn:Eb.
  - destruct c eqn:Ec.
    { destruct d eqn:Ed.
      - reflexivity.
      - reflexivity. }
    { destruct d eqn:Ed.
      - reflexivity.
      - reflexivity. }
  - destruct c eqn:Ec.
    { destruct d eqn:Ed.
      - reflexivity.
      - reflexivity. }
    { destruct d eqn:Ed.
      - reflexivity.
      - reflexivity. }
Qed.

Theorem andb_true_elim2 : forall b c : bool,
  andb2 b c = true -> c = true.
Proof.
  intros. destruct b eqn : Eb.
  - apply H.
  - destruct c eqn : Ec.
    + reflexivity.
    + rewrite<- H. simpl. reflexivity.
Qed.


Theorem zero_nbeq_plus_1 : forall n : nat,
  0 =? (n + 1) = false.
Proof.
  intros [|n'].
  - reflexivity.
  - reflexivity.
Qed.