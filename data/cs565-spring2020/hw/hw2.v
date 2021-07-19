Set Implicit Arguments.
Require Import Omega.
Require Import Coq.Strings.String.

Module ArithWithConstants.
(*  For this homework, we will consider how we might reason about a
 *  a simple language of arithmetic expressions. *)

  Inductive arith : Set :=
  | Const (n : nat)
  | Plus (e1 e2 : arith)
  | Times (e1 e2 : arith).

  (* Here are a few examples of specific expressions. *)
  Example ex1 := Const 42.
  Example ex2 := Plus (Const 1) (Times (Const 2) (Const 3)).

  (* Write a definition that computes the size of an arithmetic expression
   * This should be equivalent to the size of the expression's abstract syntax tree
   *) 
  Fixpoint size (e : arith) : nat.  Admitted.
  
  (* What is the longest path from the root of a syntax tree to a leaf? *)
  Fixpoint depth (e : arith) : nat. Admitted.

  Theorem depth_le_size : forall e, depth e <= size e.
  Proof.
    (* you may need to use the omega tactic in this proof. *)
    (* SearchAbout is also your friend! *)
  Admitted.

  (* A simple property about expressions - arguments can be swapped in 
     a commutative operation *)
  Fixpoint commuter (e : arith) : arith :=
    match e with
    | Const _ => e
    | Plus e1 e2 => Plus (commuter e2) (commuter e1)
    | Times e1 e2 => Times (commuter e2) (commuter e1)
    end.

  Theorem size_commuter : forall e, size (commuter e) = size e.
  Proof. Admitted.

  Theorem depth_commuter : forall e, depth (commuter e) = depth e.
  Proof. Admitted.
  
  Theorem commuter_involutive : forall e, commuter (commuter e) = e.
  Proof. Admitted.

End ArithWithConstants.

Module ArithWithVariables.

  Notation var := string.
  Definition var_eq : forall x y : var, {x = y} + {x <> y} := string_dec.

  Infix "==v" := var_eq (no associativity, at level 50).

  (* We now extend the language to support variables *)
  Inductive arith : Set :=
  | Const (n : nat)
  | Var (x : var) (* <-- this is the new constructor! *)
  | Plus (e1 e2 : arith)
  | Times (e1 e2 : arith).

  Fixpoint size (e : arith) : nat. Admitted.

  Fixpoint depth (e : arith) : nat. Admitted.

  (* This operator replaces all variable occurrences with arithmetic expressions *)
  Fixpoint substitute (inThis : arith) (replaceThis : var) (withThis : arith) : arith :=
    match inThis with
    | Const _ => inThis
    | Var x => if x ==v replaceThis then withThis else inThis
    | Plus e1 e2 => Plus (substitute e1 replaceThis withThis) (substitute e2 replaceThis withThis)
    | Times e1 e2 => Times (substitute e1 replaceThis withThis) (substitute e2 replaceThis withThis)
    end.

  Fixpoint commuter (e : arith) : arith :=
    match e with
    | Const _ => e
    | Var _ => e
    | Plus e1 e2 => Plus (commuter e2) (commuter e1)
    | Times e1 e2 => Times (commuter e2) (commuter e1)
    end.

  
  Theorem substitute_depth : forall replaceThis withThis inThis,
    depth (substitute inThis replaceThis withThis) <= depth inThis + depth withThis.
  Proof.  Admitted.
    
  Theorem substitute_commuter : forall replaceThis withThis inThis,
      commuter (substitute inThis replaceThis withThis) = substitute (commuter inThis) replaceThis (commuter withThis).
  Proof. Admitted.

End ArithWithVariables.    
