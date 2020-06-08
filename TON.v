Require Import Coq.Bool.Bool.
From Coq Require Import Lists.List.
From Coq Require Import Arith.Arith.
From Coq Require Import omega.Omega.

Definition BVar := nat -> bool. 
Definition NVar := nat -> nat. 
Definition Time := nat. 
Variable f : nat -> Time. 
Hypothesis f_mon : forall t, f t < f (t+1).

Record RSflipflop := { 
  rsff_R:BVar; 
  rsff_S:BVar; 
  rsff_Q:BVar; 
  rsff_spec : forall n, rsff_Q n = negb (rsff_R n)&&(rsff_S n||rsff_Q (n-1))
}.

Record TONTimer (PT : nat) := { 
  tont_IN : BVar; 
  tont_Q : BVar; 
  tont_spec_Reset : forall n, tont_IN n = false -> tont_Q n = false; 
  tont_spec_Set : forall n1 n2, PT <= f(pred n2) - f(pred n1)->tont_Q n2 = true;
  (*tont_spec_SetR : ...*)
}.

Record TranSys := { 
  States : Set; 
  Labels : Set; 
  InitState : States; 
  Trans : States -> list (Labels * States)
}.

Inductive Valve_Ss : Set :=
  q1|q2|q3|q4|q5. 

Inductive Valve_Ls : Set := 
  open | opened | timeout | close | closed. 

Definition Valve_Trans s := 
  match s with 
    | q1 => (open,q2)::nil 
    | q2 => (opened,q3)::(timeout,q5)::nil 
    | q3 => (close,q4)::nil 
    | q4 => (closed,q1)::(timeout,q5)::nil 
    | q5 => nil 
  end.

Definition ValveTransSys := 
  Build_TranSys Valve_Ss Valve_Ls q1 Valve_Trans.

Definition eq_same(v1 v2 : BVar) := 
  forall i, v1 i = v2 i. 

Definition eq_one_unit_delay(v1 v2 : BVar) := 
  forall i, v1 i = v2 (i + 1).

Notation "a '[=]' b" := (eq_same a b)(at level 50) : type_scope.
Notation "a '[=1]' b" := (eq_one_unit_delay a b)(at level 50) : type_scope.

Record WaveGen (T:Time) := {
  wg_EN : BVar;
  wg_Q : BVar;
  (*wg_spec : forall n : wg_EN n = true /\ f T = n-> wg_Q n = true;*)
}.

Reserved Notation "st '=[' c ']=>' st'"
                  (at level 40).

Definition Gen_WaveGen : forall (T : Time) (timer : TONTimer T)(rs : RSflipflop), 
  (rs.(rsff_R) [=] timer.(tont_Q _)) /\ (rs.(rsff_Q) [=1] [1] timer.(tont_IN _)) 
  -> WaveGen T.