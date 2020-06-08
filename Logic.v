Set Warnings "-notation-overridden,-parsing".
From LF Require Export Tactics.

Definition is_three (n : nat) : Prop :=
  n = 3.
Check is_three.

Definition injective {A B} (f : A -> B) :=
  forall x y : A, f x = f y -> x = y.
Lemma succ_inj : injective S.
Proof.
  intros n m H. injection H as H1. apply H1.
Qed.

Example and_example :3+4=7 /\ 2*2=4.
Proof.
  split.
  - reflexivity.
  - reflexivity.
Qed.

Lemma and_intro : forall A B : Prop, A->B->A/\B.
Proof.
  intros. split.
  - apply H.
  - apply H0.
Qed.

Example and_example' : 3+4=7 /\ 2*2=4.
Proof.
  apply and_intro.
  - reflexivity.
  - reflexivity.
Qed.

Example and_exercise :
  forall n m : nat, n + m = 0 -> n = 0 /\ m = 0.
Proof.
  (* 请在此处解答 *) Admitted.

Lemma and_example2 :
  forall n m : nat, n = 0 /\ m = 0 -> n + m = 0.
Proof.
  intros n m H.
  destruct H.
  rewrite H. rewrite H0.
  reflexivity.
Qed.

Lemma and_example3 :
  forall n m : nat, n + m = 0 -> n * m = 0.
Proof.
  intros n m H.
  assert (H' : n = 0 /\ m = 0).
  { apply and_exercise. apply H. }
  destruct H' as [Hn Hm].
  rewrite Hn. reflexivity.
Qed.

Lemma proj1 : forall P Q : Prop,
  P /\ Q -> P.
Proof.
  intros P Q [HP HQ].
  apply HP. Qed.

Lemma proj2 : forall P Q : Prop,
  P /\ Q ->Q.
Proof.
  intros P Q [HP HQ].
  apply HQ.
Qed.

Theorem and_commut : forall P Q : Prop,
  P /\ Q -> Q /\ P.
Proof.
  intros P Q [HP HQ].
  split.
  - apply HQ.
  - apply HP.
Qed.

Theorem and_assoc : forall P Q R : Prop,
  P /\ (Q /\ R) -> (P /\ Q) /\ R.
Proof.
  intros P Q R [HP [HQ HR]].
  split.
  - split.
    * apply HP.
    * apply HQ.
  - apply HR.
Qed.

Lemma or_example:
  forall n m:nat, n=0 \/ m=0 -> n*m=0.
Proof.
  intros n m [Hn | Hm].
  - rewrite Hn. reflexivity.
  - rewrite Hm. rewrite<-mult_n_O. reflexivity.
Qed.

Lemma zero_or_succ :
  forall n : nat, n = 0 \/ n = S (pred n).
Proof.
  (* 课上已完成 *)
  intros [|n].
  - left. reflexivity.
  - right. reflexivity.
Qed.

Module MyNot.
Definition not (P:Prop) := P -> False.
Notation "~ x" := (not x) : type_scope.
Check not.
(* ===> Prop -> Prop *)
End MyNot.

Theorem ex_falso_quodlibet : forall(P:Prop),
  False -> P.
Proof.
  (* 课上已完成 *)
  intros P contra.
  destruct contra. Qed.

Fact not_implies_our_not : forall (P:Prop),
  ~P -> (forall (Q:Prop), P -> Q).
Proof.
  intros.
  apply H in H0.
  destruct H0.
Qed.

Notation "x <> y" := (~(x = y)).

Theorem not_Flase :
  ~ False.
Proof.
  unfold not. intros. apply H. 
Qed.

(*将蕴含的前提推导为false，用destruct即可。*)
(*2019.7.19*)
Theorem contradiction_implies_anything :
  forall P Q:Prop, (P /\ ~P) -> Q.
Proof.
  intros. destruct H.
  apply H0 in H.
  destruct H.
Qed.

Theorem double_neg : forall P: Prop,
  P -> ~~P.
Proof.
  intros.
  unfold not.
  intros H1.
  apply H1 in H.
  destruct H.
Qed.

Theorem contrapositive : forall (P Q : Prop),
  (P -> Q) -> (~ Q -> ~ P).
Proof.
  intros. 
  unfold not.
  intros H1.
  apply H in H1.
  apply H0 in H1.
  destruct H1.
Qed.

Theorem not_both_true_and_false : forall P : Prop,
  ~ (P /\ ~P).
Proof.
  unfold not.
  intros.
  destruct H.
  apply H0 in H.
  destruct H.
Qed.
  
Theorem not_true_is_false : forall b : bool,
  b <> true -> b = false.
Proof.
  intros [] H.
  - (* b = true *)
    unfold not in H.
    (*现在已知前提是假的，就可以推出假的结论*)
    (*2019.7.19*)
    apply ex_falso_quodlibet.
    apply H. reflexivity.
  - (* b = false *)
    reflexivity.
Qed.

Theorem not_true_is_false' : forall b : bool,
  b <> true -> b = false.
Proof.
  intros [] H.
  - (* b = true *)
    unfold not in H.
    exfalso. (* <=== *)
    apply H. reflexivity.
  - (* b = false *) reflexivity.
Qed.

Lemma True_is_true : True.
Proof. apply I. Qed.

Module MyIff.

Definition iff (P Q : Prop) := (P -> Q) /\ (Q -> P).

Notation "P <-> Q" := (iff P Q)
                      (at level 95, no associativity)
                      : type_scope.

End MyIff.

Theorem iff_sym : forall P Q : Prop,
  (P <-> Q) -> (Q <-> P).
Proof.
  (* 课上已完成 *)
  intros P Q [HAB HBA].
  split.
  - (* -> *) apply HBA.
  - (* <- *) apply HAB. 
Qed.

(*当且仅当出现在条件中时用destruct,结论中时用split.*)
(*2019.7.19*)
Lemma not_true_iff_false : forall b,
  b <> true <-> b = false.
Proof.
  (* 课上已完成 *)
  intros b. split.
  - (* -> *) apply not_true_is_false.
  - (* <- *)
    intros H. rewrite H. intros H'. discriminate H'.
Qed.


Theorem or_distributes_over_and : forall P Q R : Prop,
  P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof.
  intros P Q R. split.
  - intros [HP|[HQ HR]].
    * split.
      + left. apply HP.
      + left. apply HP.
    * split.
      + right. apply HQ.
      + right. apply HR.
  - intros [[HP1|HQ1][|HR1]]. 
    + left. apply H.
    + left. apply HP1.
    + left. apply H.
    + right.  split.
        * apply HQ1.
        * apply HR1.
Qed.            
  
From Coq Require Import Setoids.Setoid.
Lemma mult_0 : forall n m, n * m = 0 <-> n = 0 \/ m = 0.
Proof.
  split.
  - intros. destruct n as [| n'].
    + left. reflexivity.
    + right. destruct m.
      * reflexivity.
      * discriminate.
  - apply or_example.
Qed.

Lemma or_assoc :
  forall P Q R : Prop, P \/ (Q \/ R) <-> (P \/ Q) \/ R.
Proof.
  intros P Q R. split.
  - intros [H | [H | H]].
    + left. left. apply H.
    + left. right. apply H.
    + right. apply H.
  - intros [[H | H] | H].
    + left. apply H.
    + right. left. apply H.
    + right. right. apply H.
Qed.

Lemma mult_0_3 :
  forall n m p, n * m * p = 0 <-> n = 0 \/ m = 0 \/ p = 0.
Proof.
  intros n m p.
  rewrite mult_0. rewrite mult_0. rewrite or_assoc.
  reflexivity.
Qed.

Lemma apply_iff_example :
  forall n m : nat, n * m = 0 -> n = 0 \/ m = 0.
Proof.
  intros n m H. apply mult_0. apply H.
Qed.

Lemma four_is_even : exists n : nat, 4 = n + n.
Proof.
  exists 2. reflexivity.
Qed.

Theorem exists_example_2 : forall n,
  (exists m, n = 4 + m) ->
  (exists o, n = 2 + o).
Proof.
  (* 课上已完成 *)
  intros n [m Hm]. (* 注意这里隐式使用了 destruct *)
  exists (2 + m).
  apply Hm.
Qed.

Theorem dist_not_exists : forall (X:Type) (P : X -> Prop),
  (forall x, P x) -> ~ (exists x, ~ P x).
Proof.
  intros. unfold not.
  intros H1. destruct H1.
  apply H0 in H.
  apply H.
Qed.

(*只有在引入一个特例，出现exists x0时，才能使用exists x.语句*)
(*这个特例通常由假设destruct而来*)
(*2019.7.19*) 
Theorem dist_exists_or : forall (X:Type) (P Q : X -> Prop),
  (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof.
  split.
  - intros. destruct H. destruct H.
      + left. exists x. apply H.
      + right. exists x. apply H.
  - intros. inversion H as [HP|HQ]. 
      + destruct HP as [x Hx]. exists x. left. apply Hx.
      + destruct HQ as [x Hx]. exists x. right. apply Hx.
Qed.

Fixpoint In {A : Type} (x : A) (l : list A) : Prop :=
  match l with
  | [] => False
  | x' :: l' => x' = x \/ In x l'
  end.

Example In_example_1 : In 4 [1; 2; 3; 4; 5].
Proof.
  unfold In. right. right. right. left. reflexivity.
Qed.

Example In_example_2 :
  forall n, In n [2; 4] ->
  exists n', n = 2 * n'.
Proof.
  simpl.
  intros. destruct H as [H|[H1|H2]].
  - exists 1. rewrite <- H. reflexivity.
  - exists 2. rewrite <- H1. reflexivity.
  - destruct H2.
Qed.

Lemma In_map :
  forall (A B : Type) (f : A -> B) (l : list A) (x : A),
    In x l ->
    In (f x) (map f l).
Proof.
  intros A B f l x.
  induction l as [|x' l' IHl'].
  - (* l = nil，矛盾 *)
    simpl. intros [].
  - (* l = x' :: l' *)
    simpl. intros [H | H].
    + rewrite H. left. reflexivity.
    + right. apply IHl'. apply H.
Qed.

(*当exists 出现在条件中时，可通过intros [x [H1 H2]]来引入*)
(*2019.7.20*)
Lemma In_map_iff :
  forall (A B : Type) (f : A -> B) (l : list A) (y : B),
    In y (map f l) <->
    exists x, f x = y /\ In x l.
Proof.
  intros. split.
  induction l as [|h t].
  - simpl. intros [].
  - simpl. intros [H | H].
    + exists h. split. apply H. left. reflexivity.
    + apply IHt in H. destruct H as [w [F I]].
      exists w. split. apply F. right. apply I.
  - intros [w [F I]].
    rewrite <- F. apply In_map. apply I.
Qed.
    
Lemma In_app_iff : forall A l l' (a:A),
  In a (l++l') <-> In a l \/ In a l'.
Proof.
  intros. split.
  - induction l as [|h t].
    + simpl. intros. right. apply H.
    + simpl. intros. destruct H as [H1|H2].
      * left. left. apply H1.
      * apply IHt in H2. destruct H2 as [H3|H4].
        {left. right. apply H3. }
        {right. apply H4. }
  - induction l as [|h t].
    + simpl. intros [|H5]. 
      * destruct H.
      * apply H5.
    + intros [H7|H7].
      * simpl. inversion H7. left. apply H. 
        right. apply IHt. left. apply H.
      * simpl. right. apply IHt. right. apply H7.
Qed.

Fixpoint All {T : Type} (P : T -> Prop) (l : list T) : Prop :=
  match l with
  | [] => True
  | h :: t => P h /\ All P t
  end.

Lemma All_In :
  forall T (P : T -> Prop) (l : list T),
    (forall x, In x l -> P x) <->
    All P l.
Proof.
  intros. split.
  - induction l as [|h t].
    + simpl. reflexivity.
    + simpl. intros. split.
      * apply H. left. reflexivity.
      * apply IHt. intros. apply H. right. apply H0.
  - induction l as [|h t].
    + simpl. intros. destruct H0.
    + simpl. intros. apply IHt.
      * apply H.
      * Admitted.

Print All_In.

Definition combine_odd_even (Podd Peven : nat -> Prop) : nat -> Prop
  (* 将本行替换成 ":= _你的_定义_ ." *). Admitted.

Theorem combine_odd_even_intro :
  forall (Podd Peven : nat -> Prop) (n : nat),
    (oddb n = true -> Podd n) ->
    (oddb n = false -> Peven n) ->
    combine_odd_even Podd Peven n.
Proof.
  (* 请在此处解答 *) Admitted.
Theorem combine_odd_even_elim_odd :
  forall (Podd Peven : nat -> Prop) (n : nat),
    combine_odd_even Podd Peven n ->
    oddb n = true ->
    Podd n.
Proof.
  (* 请在此处解答 *) Admitted.
Theorem combine_odd_even_elim_even :
  forall (Podd Peven : nat -> Prop) (n : nat),
    combine_odd_even Podd Peven n ->
    oddb n = false ->
    Peven n.
Proof.
  (* 请在此处解答 *) Admitted.

Lemma plus_comm3_take3 :
  forall x y z, x + (y + z) = (z + y) + x.
Proof.
  intros x y z.
  rewrite plus_comm.
  rewrite (plus_comm y z).
  reflexivity.
Qed.

Lemma in_not_nil :
  forall A (x : A) (l : list A), In x l -> l <> [].
Proof.
  intros A x l H. unfold not. intro Hl. destruct l.
  - simpl in H. destruct H.
  - discriminate Hl.
Qed.
(*当条件中出现类似Sn = 0时，直接使用discriminate指令可完成证明*)

Lemma in_not_nil_42 :
  forall l : list nat, In 42 l -> l <> [].
Proof.
  (* 课上已完成 *)
  intros l H.
  Fail apply in_not_nil.
Abort.
(* apply ... with ... *)
Lemma in_not_nil_42_take2 :
  forall l : list nat, In 42 l -> l <> [].
Proof.
  intros l H.
  apply in_not_nil with (x := 42).
  apply H.
Qed.
(* apply ... in ... *)
Lemma in_not_nil_42_take3 :
  forall l : list nat, In 42 l -> l <> [].
Proof.
  intros l H.
  apply in_not_nil in H.
  apply H.
Qed.
(* 显式地对 x 的值应用引理。 *)
Lemma in_not_nil_42_take4 :
  forall l : list nat, In 42 l -> l <> [].
Proof.
  intros l H.
  apply (in_not_nil nat 42).
  apply H.
Qed.
(* 显式地对假设应用引理。 *)
Lemma in_not_nil_42_take5 :
  forall l : list nat, In 42 l -> l <> [].
Proof.
  intros l H.
  apply (in_not_nil _ _ _ H).
Qed.

Example lemma_application_ex :
  forall {n : nat} {ns : list nat},
    In n (map (fun m => m * 0) ns) ->
    n = 0.
Proof.
  intros n ns H.
  destruct (proj1 _ _ (In_map_iff _ _ _ _ _) H)
           as [m [Hm _]].
  rewrite mult_0_r in Hm. rewrite <- Hm. reflexivity.
Qed.

Axiom functional_extensionality : forall {X Y: Type}
                                    {f g : X -> Y},
  (forall (x:X), f x = g x) -> f = g.

Example function_equality_ex2 :
  (fun x => plus x 1) = (fun x => plus 1 x).
Proof.
  apply functional_extensionality. intros x.
  apply plus_comm.
Qed.

Print Assumptions function_equality_ex2.

Fixpoint rev_append {X} (l1 l2 : list X) : list X :=
  match l1 with
  | [] => l2
  | x :: l1' => rev_append l1' (x :: l2)
  end.
Definition tr_rev {X} (l : list X) : list X :=
  rev_append l [].

Lemma tr_rev_correct : forall X, @tr_rev X = @rev X.
Proof.
  intros. apply functional_extensionality. induction x.
  - simpl. unfold tr_rev. simpl. reflexivity.
  - simpl. rewrite <- IHx. unfold tr_rev. simpl. 
    assert (H : [x] = [] ++ [x]). { simpl. reflexivity. }
    Admitted.
  
Theorem evenb_double : forall k, evenb (double k) = true.
Proof.
  intros k. induction k as [|k' IHk'].
  - reflexivity.
  - simpl. apply IHk'.
Qed.

Theorem evenb_double_conv : forall n,
  exists k, n = if evenb n then double k
                else S (double k).
Proof.
  intros. induction n.
  - exists 0. simpl. reflexivity.
  - rewrite evenb_S. destruct (evenb n).
    + destruct IHn. rewrite H. simpl. exists x. reflexivity.
    + destruct IHn. simpl. rewrite H. exists (S x). simpl. reflexivity.
Qed.

Theorem even_bool_prop : forall n,
  evenb n = true <-> exists k, n = double k.
Proof.
  intros n. split.
  - intros H. destruct (evenb_double_conv n) as [k Hk].
    rewrite Hk. rewrite H. exists k. reflexivity.
  - intros [k Hk]. rewrite Hk. apply evenb_double.
Qed.

Theorem eqb_eq : forall n1 n2 : nat,
  n1 =? n2 = true <-> n1 = n2.
Proof.
  intros n1 n2. split.
  - apply eqb_true.
  - intros H. rewrite H. Admitted.

Inductive reg_exp {T : Type} : Type :=
  | EmptySet
  | EmptyStr
  | Char (t : T)
  | App (r1 r2 : reg_exp)
  | Union (r1 r2 : reg_exp)
  | Star (r : reg_exp).

Inductive exp_match {T} : list T -> reg_exp -> Prop :=
  | MEmpty : exp_match [] EmptyStr
  | MChar x : exp_match [x] (Char x)
  | MApp s1 re1 s2 re2
             (H1 : exp_match s1 re1)
             (H2 : exp_match s2 re2) :
             exp_match (s1 ++ s2) (App re1 re2)
  | MUnionL s1 re1 re2
                (H1 : exp_match s1 re1) :
                exp_match s1 (Union re1 re2)
  | MUnionR re1 s2 re2
                (H2 : exp_match s2 re2) :
                exp_match s2 (Union re1 re2)
  | MStar0 re : exp_match [] (Star re)
  | MStarApp s1 s2 re
                 (H1 : exp_match s1 re)
                 (H2 : exp_match s2 (Star re)) :
                 exp_match (s1 ++ s2) (Star re).

Notation "s =~ re" := (exp_match s re) (at level 80).

Example reg_exp_ex1 : [1] =~ Char 1.
Proof.
  apply MChar.
Qed.

Example reg_exp_ex2 : [1; 2] =~ App (Char 1) (Char 2).
Proof.
  apply (MApp [1] _ [2]).
  - apply MChar.
  - apply MChar.
Qed.

Fixpoint reg_exp_of_list {T} (l : list T) :=
  match l with
  | [] => EmptyStr
  | x :: l' => App (Char x) (reg_exp_of_list l')
  end.
Example reg_exp_ex4 : [1; 2; 3] =~ reg_exp_of_list [1; 2; 3].
Proof.
  simpl. apply (MApp [1]).
  { apply MChar. }
  apply (MApp [2]).
  { apply MChar. }
  apply (MApp [3]).
  { apply MChar. }
  apply MEmpty.
Qed.

Lemma MStar1 :
  forall T s (re : @reg_exp T) ,
    s =~ re ->
    s =~ Star re.
Proof.
  intros T s re H.
  rewrite <- (app_nil_r _ s).
  apply (MStarApp s [] re).
  - apply H.
  - apply MStar0.
Qed.


Lemma MUnion' : forall T (s : list T) (re1 re2 : @reg_exp T),
  s =~ re1 \/ s =~ re2 ->
  s =~ Union re1 re2.
Proof.
  intros. destruct H.
  - apply MUnionL re1.