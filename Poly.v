Set Warnings "-notation-overridden,-parsing".
From LF Require Export Lists.

Inductive list (X:Type) : Type :=
  | nil
  | cons (x : X) (l : list X).

Arguments nil {X}.
Arguments cons {X} _ _.

Fixpoint repeat {X : Type} (x : X) (count : nat) : list X :=
  match count with
  | 0 => nil
  | S count' => cons x (repeat x count')
  end.

Fixpoint app {X : Type} (l1 l2 : list X) : (list X) :=
  match l1 with
  | nil => l2
  | cons h t => cons h (app t l2)
  end.

Fixpoint rev {X:Type} (l:list X) : list X :=
  match l with
  | nil => nil
  | cons h t => app (rev t) (cons h nil)
  end.

Fixpoint length {X : Type} (l : list X) : nat :=
  match l with
  | nil => 0
  | cons _ l' => S (length l')
  end.

Notation "x :: y" := (cons x y)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y)
                     (at level 60, right associativity).

(*对隐式参数类型的定理进行证明时，要将类型名也用intros指令引入。*)
(*类型名必须放在首位。系统将首个字母自动识别为类型名。*)
Theorem app_nil_r : forall (X:Type), forall l:list X,
  l ++ [] = l.
Proof.
  intros X l. 
  induction l as [| n l' IHl].
  - reflexivity.
  - simpl. rewrite->IHl. reflexivity.
Qed.

Theorem app_assoc : forall A (l m n:list A),
  l ++ m ++ n = (l ++ m) ++ n.
Proof.
  intros A l m n.
  induction l as [|x l' IHl].
  - simpl. reflexivity.
  - simpl. rewrite<- IHl. reflexivity.
Qed.

Lemma app_length : forall(X:Type) (l1 l2 : list X),
  length (l1 ++ l2) = length l1 + length l2.
Proof.
  intros X l1 l2.
  induction l1 as [| n l1' IHl1].
  - simpl. reflexivity.
  - simpl. rewrite->IHl1. reflexivity.
Qed.

Lemma rev_app_distr_lemma :forall X (l1 l2 : list X),
  (rev l1 ++ rev l2) = rev l1 ++ rev l2.
Proof.
  intros. reflexivity.
Qed.

Theorem rev_app_distr: forall X (l1 l2 : list X),
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  intros X l1 l2.
  induction l1 as [| n l1' IHl1].
  - simpl. rewrite->app_nil_r. reflexivity.
  - simpl. rewrite->IHl1. rewrite->app_assoc. reflexivity.
Qed.


Theorem rev_involutive : forall X : Type, forall l : list X,
  rev (rev l) = l.
Proof.
  intros X l .
  induction l as [| n l' IHl].
  - simpl. reflexivity.
  - simpl. rewrite->rev_app_distr. rewrite->IHl. reflexivity.
Qed.

Inductive prod (X Y : Type) : Type :=
| pair (x : X) (y : Y).
Arguments pair {X} {Y} _ _.

Notation "( x , y )" := (pair x y).
Notation "X * Y" := (prod X Y) : type_scope.
(*(x,y)是一个值，它由两个其它的值构造而来，X*Y是一个类型，它由其他两个类型构造而来。*)
(*若x的类型为X,y的类型为Y，(x,y)的类型为X*Y。*)
(*也就是说一个二元组的两个元素可以为不同的类型X Y，那么这个二元组的类型为X*Y。*)
Definition fst {X Y : Type} (p : X * Y) : X :=
  match p with
  | (x, y) => x
  end.

Definition snd {X Y : Type} (p : X * Y) : Y :=
  match p with
  | (x, y) => y
  end.

Fixpoint combine {X Y : Type} (lx : list X) (ly : list Y)
           : list (X*Y) :=
  match lx, ly with
  | [], _ => []
  | _, [] => []
  | x :: tx, y :: ty => (x, y) :: (combine tx ty)
  end.

Fixpoint split {X Y : Type} (l : list (X*Y))
               : (list X) * (list Y) :=
  match l with
  | [] => ([], [])
  | (x, y) :: t =>
      match split t with
      | (lx, ly) => (x :: lx, y :: ly)
      end
  end.

Example test_split:
  split [(1,false);(2,false)] = ([1;2],[false;false]).
Proof.
  simpl. reflexivity.
Qed.

Module OptionPlayground.
Inductive option (X:Type) : Type :=
  | Some (x : X)
  | None.
Arguments Some {X} _.
Arguments None {X}.
End OptionPlayground.

Fixpoint nth_error {X : Type} (l : list X) (n : nat)
                   : option X :=
  match l with
  | [] => None
  | a :: l' => if n =? O then Some a else nth_error l' (pred n)
  end.

Definition hd_error {X : Type} (l : list X) : option X :=
  match l with
  | [] => None
  | a :: l' => Some a 
  end.

Check @hd_error.
Example test_hd_error1 : hd_error [1;2] = Some 1.
Proof. reflexivity. Qed.
Example test_hd_error2 : hd_error [[1];[2]] = Some [1].
Proof. reflexivity. Qed.

Fixpoint filter {X:Type} (test: X->bool) (l:list X)
                : (list X) :=
  match l with
  | [] => []
  | h :: t => if test h then h :: (filter test t)
                        else filter test t
  end.

Example test_filter1: filter evenb [1;2;3;4] = [2;4].
Proof. reflexivity. Qed.

Definition filter_even_gt7 (l : list nat) : list nat :=
  filter (fun x =>if evenb x then negb(leb x 7) else false) l.
(*fun x => andb (negb (leb x 7) (evenb x)) 为什么不对*)
Compute filter_even_gt7 [1;2;6;9;10;3;12;8].

Example test_filter_even_gt7_1 :
  filter_even_gt7 [1;2;6;9;10;3;12;8] = [10;12;8].
Proof. reflexivity. Qed.
Example test_filter_even_gt7_2 :
  filter_even_gt7 [5;2;6;19;129] = [].
Proof. reflexivity. Qed.

Definition partition {X:Type} (test:X->bool) (l:list X)
                     : list X * list X :=
  (filter test l, filter (fun x => negb (test x)) l).

Example test_partition1: partition oddb [1;2;3;4;5] = ([1;3;5], [2;4]).
Proof. reflexivity. Qed.
Example test_partition2: partition (fun x => false) [5;9;0] = ([], [5;9;0]).
Proof. reflexivity. Qed.

Fixpoint map {X Y: Type} (f:X->Y) (l:list X) : (list Y) :=
  match l with
  | [] => []
  | h :: t => (f h) :: (map f t)
  end.

Theorem map_dispose : forall (X Y : Type) (f : X -> Y) (l1 l2 : list X),
  map f (l1 ++ l2) = map f l1 ++ map f l2.
Proof.
  intros X Y f l1 l2.
  induction l1 as [| n l1' IHl1].
  - simpl. reflexivity.
  - simpl. rewrite->IHl1. reflexivity.
Qed.

Theorem map_rev : forall (X Y : Type) (f : X -> Y) (l : list X),
  map f (rev l) = rev (map f l).
Proof.
  intros X Y f l.
  induction l as [| n l' IHl].
  - simpl. reflexivity.
  - simpl. rewrite<-IHl. rewrite->map_dispose.
        reflexivity.
Qed.

Fixpoint flat_map {X Y: Type} (f: X -> list Y) (l: list X) : (list Y) :=
  match l with
  | [] => []
  | h :: t => f h ++ flat_map f t
  end.
 
Example test_flat_map1:
  flat_map (fun n => [n;n;n]) [1;5;4]
  = [1; 1; 1; 5; 5; 5; 4; 4; 4].
Proof.
  simpl. reflexivity.
Qed.

Fixpoint fold {X Y: Type} (f: X->Y->Y) (l: list X) (b: Y)
                         : Y :=
  match l with
  | nil => b
  | h :: t => f h (fold f t b)
  end.

Module Exercise.

Definition fold_length {X: Type} (l : list X) : nat :=
  fold (fun _ n => S n) l 0.

Theorem fold_length_correct : forall X (l:list X),
  fold_length l = length l.
Proof.
  intros X l.
  induction l as [| n l' IHl].
  - simpl. reflexivity.
  - simpl. rewrite<-IHl. reflexivity.
Qed.

Definition fold_map {X Y: Type} (f: X -> Y) (l: list X) : list Y
  (* 将本行替换成 ":= _你的_定义_ ." *). Admitted.

Definition prod_curry {X Y Z : Type}
  (f : X * Y -> Z) (x : X) (y : Y) : Z := f (x, y).

Definition prod_uncurry {X Y Z : Type}
  (f : X -> Y -> Z) (p : X * Y) : Z
  := f (fst p) (snd p).

Check @prod_curry.
Check @prod_uncurry.
(*直接化简就可以了？*)
Theorem uncurry_curry : forall (X Y Z : Type)
                        (f : X -> Y -> Z)
                        x y,
  prod_curry (prod_uncurry f) x y = f x y.
Proof.
  intros. reflexivity. Qed.


Theorem curry_uncurry : forall (X Y Z : Type)
                        (f : (X * Y) -> Z) (p : X * Y),
  prod_uncurry (prod_curry f) p = f p.
Proof.
  intros. destruct p. reflexivity. Qed.
(*
Module Church.
Definition cnat := forall X : Type, (X -> X) -> X -> X.

Definition one : cnat :=
  fun (X : Type) (f : X -> X) (x : X) => f x.

Definition two : cnat :=
  fun (X : Type) (f : X -> X) (x : X) => f (f x).

Definition zero : cnat :=
  fun (X : Type) (f : X -> X) (x : X) => x.

Definition doit3times {X:Type} (f:X->X) (n:X) : X :=
  f (f (f n)).

Definition three : cnat := @doit3times.

Definition succ (n : cnat) : cnat
  (* 将本行替换成 ":= _你的_定义_ ." *). Admitted.
Example succ_1 : succ zero = one.
Proof. (* 请在此处解答 *) Admitted.
Example succ_2 : succ one = two.
Proof. (* 请在此处解答 *) Admitted.
Example succ_3 : succ two = three.
Proof. (* 请在此处解答 *) Admitted.

Definition plus (n m : cnat) : cnat
  (* 将本行替换成 ":= _你的_定义_ ." *). Admitted.
Example plus_1 : plus zero one = one.
Proof. (* 请在此处解答 *) Admitted.
Example plus_2 : plus two three = plus three two.
Proof. (* 请在此处解答 *) Admitted.
Example plus_3 :
  plus (plus two two) three = plus one (plus three three).
Proof. (* 请在此处解答 *) Admitted.

Definition mult (n m : cnat) : cnat
  (* 将本行替换成 ":= _你的_定义_ ." *). Admitted.
Example mult_1 : mult one one = one.
Proof. (* 请在此处解答 *) Admitted.
Example mult_2 : mult zero (plus three three) = zero.
Proof. (* 请在此处解答 *) Admitted.
Example mult_3 : mult two three = plus three three.
Proof. (* 请在此处解答 *) Admitted.

Definition exp (n m : cnat) : cnat
  (* 将本行替换成 ":= _你的_定义_ ." *). Admitted.
Example exp_1 : exp two two = plus two two.
Proof. (* 请在此处解答 *) Admitted.
Example exp_2 : exp three zero = one.
Proof. (* 请在此处解答 *) Admitted.
Example exp_3 : exp three two = plus (mult two (mult two two)) one.
Proof. (* 请在此处解答 *) Admitted.

End Church.*)
End Exercise.