Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import Init.Nat.
From Coq Require Import omega.Omega.
From Coq Require Import Lists.List.
Import ListNotations.
Require Import Maps.
Require Import Smallstep.
Require Import Types.
Require Import Imp.

Hint Constructors multi.

Module S.

Import Smallstep.

Definition stack := list nat.
Definition prog  := list sinstr.

Inductive stack_step : state -> prog * stack -> prog * stack -> Prop :=
  | SS_Push : forall st stk n p',
    stack_step st (SPush n :: p', stk)      (p', n :: stk)
  | SS_Load : forall st stk i p',
    stack_step st (SLoad i :: p', stk)      (p', st i :: stk)
  | SS_Plus : forall st stk n m p',
    stack_step st (SPlus :: p', n::m::stk)  (p', (m+n)::stk)
  | SS_Minus : forall st stk n m p',
    stack_step st (SMinus :: p', n::m::stk) (p', (m-n)::stk)
  | SS_Mult : forall st stk n m p',
    stack_step st (SMult :: p', n::m::stk)  (p', (m*n)::stk).

Theorem stack_step_deterministic : forall st,
  deterministic (stack_step st).
Proof.
Admitted.

Definition stack_multistep st := multi (stack_step st).

Definition compiler_is_correct_statement : Prop :=
  forall (st : state) (e : aexp),
    stack_multistep st (s_compile e, []) ([], [ aeval st e ]).

Theorem s_compile_aux : forall (e : aexp) (t: prog) (st : state) (stk1 : stack),
  stack_multistep st (s_compile e ++ t, stk1) (t, aeval st e :: stk1).
Proof.
Admitted.

Theorem compiler_is_correct : compiler_is_correct_statement.
Proof.
  Admitted.

End S.

Module T.

Import Types.

Theorem progress : forall t T,
  |- t \in T ->
  value t \/ exists t', t --> t'.

Proof with auto.
  intros t T HT.
  induction HT...
  (* The cases that were obviously values, like T_Tru and
     T_Fls, were eliminated immediately by auto *)
  - (* T_Test *)
    right. inversion IHHT1; clear IHHT1.
    + (* t1 is a value *)
    apply (bool_canonical t1 HT1) in H.
    inversion H; subst; clear H.
      exists t2...
      exists t3...
    + (* t1 can take a step *)
      inversion H as [t1' H1].
       exists (test t1' t2 t3)...
    Admitted.    


Theorem preservation : forall t t' T,
  |- t \in T ->
  t --> t' ->
  |- t' \in T.

Proof with auto.
  intros t t' T HT HE.
  generalize dependent t'.
  induction HT;
         (* every case needs to introduce a couple of things *)
         intros t' HE;
         (* and we can deal with several impossible
            cases all at once *)
         try solve_by_invert.
    - (* T_Test *) inversion HE; subst; clear HE.
      + (* ST_TESTTru *) assumption.
      + (* ST_TestFls *) assumption.
      + (* ST_Test *) apply T_Test; try assumption.
        apply IHHT1; assumption.
    (* FILL IN HERE *) Admitted.
(** [] *)

  
End T.

