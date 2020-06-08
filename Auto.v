Set Warnings "-notation-overridden,-parsing".
From Coq Require Import omega.Omega.
From LF Require Import Maps.
From LF Require Import Imp.

Ltac inv H := inversion H; subst; clear H.
Theorem ceval_deterministic: forall c st st1 st2,
    st =[ c ]=> st1 ->
    st =[ c ]=> st2 ->
    st1 = st2.
Proof.
  intros c st st1 st2 E1 E2;
  generalize dependent st2;
  induction E1; intros st2 E2; inv E2.
  - (* E_Skip *) reflexivity.
  - (* E_Ass *) reflexivity.
  - (* E_Seq *)
    assert (st' = st'0) as EQ1.
    { (* 断言的证明 *) apply IHE1_1; apply H1. }
    subst st'0.
    apply IHE1_2. assumption.
  (* E_IfTrue *)
  - (* b 求值为 true *)
    apply IHE1. assumption.
  - (* b 求值为 false（矛盾） *)
    rewrite H in H5. inversion H5.
  (* E_IfFalse *)
  - (* b 求值为 false（矛盾） *)
    rewrite H in H5. inversion H5.
  - (* b 求值为 false *)
    apply IHE1. assumption.
  (* E_WhileFalse *)
  - (* b 求值为 false *)
    reflexivity.
  - (* b 求值为 true（矛盾） *)
    rewrite H in H2. inversion H2.
  (* E_WhileTrue *)
  - (* b 求值为 false（矛盾） *)
    rewrite H in H4. inversion H4.
  - (* b 求值为 true *)
    assert (st' = st'0) as EQ1.
    { (* 断言的证明 *) apply IHE1_1; assumption. }
    subst st'0.
    apply IHE1_2. assumption. Qed.

Example auto_example_1 : forall (P Q R: Prop),
  (P -> Q) -> (Q -> R) -> P -> R.
Proof.
  intros P Q R H1 H2 H3.
  apply H2. apply H1. assumption.
Qed.

Example auto_example_2 : forall (P Q R: Prop),
  (P -> Q) -> (Q -> R) -> P -> R.
Proof.
  auto.
Qed.

Example auto_example_4 : forall P Q R : Prop,
  Q ->
  (Q -> R) ->
  P \/ (Q /\ R).
Proof. auto. Qed.

Lemma le_antisym : forall n m: nat, (n <= m /\ m <= n) -> n = m.
Proof. intros. omega. Qed.
Example auto_example_6 : forall n m p : nat,
  (n <= p -> (n <= m /\ m <= n)) ->
  n <= p ->
  n = m.
Proof.
  intros.
  auto using le_antisym.
Qed.

Theorem ceval_deterministic': forall c st st1 st2,
    st =[ c ]=> st1 ->
    st =[ c ]=> st2 ->
    st1 = st2.
Proof.
  intros c st st1 st2 E1 E2.
  generalize dependent st2;
       induction E1; intros st2 E2; inv E2; auto.
  - (* E_Seq *)
    assert (st' = st'0) as EQ1 by auto.
    subst st'0.
    auto.
  - (* E_IfTrue *)
    + (* b 求值为 false（矛盾） *)
      rewrite H in H5. inversion H5.
  - (* E_IfFalse *)
    + (* b 求值为 true（矛盾） *)
      rewrite H in H5. inversion H5.
  - (* E_WhileFalse *)
    + (* b 求值为 true（矛盾） *)
      rewrite H in H2. inversion H2.
  (* E_WhileTrue *)
  - (* b 求值为 false（矛盾） *)
    rewrite H in H4. inversion H4.
  - (* b 求值为 true *)
    assert (st' = st'0) as EQ1 by auto.
    subst st'0.
    auto.
Qed.

Ltac rwinv H1 H2 := rewrite H1 in H2; inv H2.
Theorem ceval_deterministic'': forall c st st1 st2,
    st =[ c ]=> st1 ->
    st =[ c ]=> st2 ->
    st1 = st2.
Proof.
  intros c st st1 st2 E1 E2.
  generalize dependent st2;
  induction E1; intros st2 E2; inv E2; auto.
  - (* E_Seq *)
    assert (st' = st'0) as EQ1 by auto.
    subst st'0.
    auto.
  - (* E_IfTrue *)
    + (* b 求值为 false（矛盾） *)
      rwinv H H5.
  - (* E_IfFalse *)
    + (* b 求值为 true（矛盾） *)
      rwinv H H5.
  - (* E_WhileFalse *)
    + (* b 求值为 true（矛盾） *)
      rwinv H H2.
  (* E_WhileTrue *)
  - (* b 求值为 false（矛盾） *)
    rwinv H H4.
  - (* b 求值为 true *)
    assert (st' = st'0) as EQ1 by auto.
    subst st'0.
    auto. Qed.

Ltac find_rwinv :=
  match goal with
    H1: ?E = true,
    H2: ?E = false
    |- _ => rwinv H1 H2
  end.

Theorem ceval_deterministic''': forall c st st1 st2,
    st =[ c ]=> st1 ->
    st =[ c ]=> st2 ->
    st1 = st2.
Proof.
  intros c st st1 st2 E1 E2.
  generalize dependent st2;
  induction E1; intros st2 E2; inv E2; try find_rwinv; auto.
  - (* E_Seq *)
    assert (st' = st'0) as EQ1 by auto.
    subst st'0.
    auto.
  - (* E_WhileTrue *)
    + (* b 求值为 true *)
      assert (st' = st'0) as EQ1 by auto.
      subst st'0.
      auto. Qed.

