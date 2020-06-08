From LF Require Export Basics.

Theorem plus_n_O : forall n : nat, n = n + 0.
Proof.
  intros n. induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite <- IHn'. reflexivity. Qed.

Theorem minus_diag : forall n : nat,
  minus n n = 0.
Proof.
  intros n. induction n as [| n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite <- IHn'. reflexivity.
  Qed.

Theorem mult_0_r : forall n : nat,
  n * 0 = 0.
Proof.
  intros n. induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite->IHn'. reflexivity.
Qed.

Theorem plus_n_Sm : forall n m : nat,
  S(n + m) = n + (S m).
Proof.
  intros n m. induction n as [| n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem plus_comm : forall n m : nat,
  n + m = m + n.
Proof.
  intros n m. induction n as [| n' IHn'].
  - simpl. rewrite<-plus_n_O. reflexivity.
  - simpl. rewrite<-plus_n_Sm. rewrite->IHn'. reflexivity.
Qed.

Theorem plus_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros n m p. induction n as [| n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite-> IHn'. reflexivity.
Qed.

Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

Lemma double_plus : forall n, double n = n + n.
Proof.
  intros n. induction n as [|n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite->IHn'. rewrite->plus_n_Sm. reflexivity.
Qed.

Lemma double_even : forall b : bool,
  negb( negb (b)) = b.
Proof.
  destruct b.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Theorem evenb_S : forall n: nat,
  evenb (S n) = negb (evenb n).
Proof.
  intros n. induction n as [|n' IHn'].
  - simpl. reflexivity.
  - rewrite IHn'. simpl. 
    rewrite double_even.
    reflexivity.
Qed.

Theorem mult_0_plus' : forall n m : nat,
  (0 + n) * m = n * m.
Proof.
  intros n m.
  assert (H: 0 + n = n). { reflexivity. }
  rewrite -> H.
  reflexivity. Qed.

Theorem plus_assoc' : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof. intros n m p. induction n as [| n' IHn']. reflexivity.
  simpl. rewrite -> IHn'. reflexivity. Qed. 

Theorem plus_swap : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
  intros.
  induction n.
  - simpl. reflexivity.
  - simpl. rewrite->IHn. rewrite->plus_n_Sm. reflexivity.
Qed.

Theorem mult_1_r : forall n : nat,
  n * 1 = n.
Proof.
  intros n. induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite->IHn'. reflexivity.
Qed.


(*destruct只能获得一个等式，induction可以获得一个假设。*)
(*通常假设会推动证明的发展。*)
(*2019.7.13*)
Theorem lemma_mult_comm : forall m n: nat,
  n + n * m = n * S m.
  intros m n.
  induction n as [|n' IHn'].
  - simpl. reflexivity. 
  - simpl. rewrite->plus_swap.
    rewrite->IHn'. reflexivity.
Qed. 

Theorem mult_comm : forall m n : nat,
  m * n = n * m.
Proof.
  intros m n.
  induction m as [|m' IHm'].
  - simpl. rewrite->mult_0_r. reflexivity.
  - simpl. rewrite-> IHm'.
    induction n as [|n' IHn'].
      * simpl. reflexivity.
      * simpl. rewrite->plus_swap.
               rewrite->lemma_mult_comm.
               reflexivity.
Qed.
