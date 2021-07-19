
Set Warnings "-notation-overridden,-parsing".

Require Import Coq.Strings.String.
Require Import Coq.Arith.Arith.
Require Import Maps.
Export List ListNotations.
Open Scope list_scope.
Open Scope string_scope.
Set Implicit Arguments.



(*  Given a boolean operator [eqb] for testing equality of elements of
    some type [A], we can define a function [eqb_list] for testing
    equality of lists with elements in [A].  Complete the definition
    of the [eqb_list] function below.  To make sure that your
    definition is correct, prove the lemma [eqb_list_true_iff]. *)

Fixpoint eqb_list {A : Type} (eqb : A -> A -> bool)
         (l1 l2 : list A) : bool :=
  match l1, l2 with
    | [], [] => true
    | a :: l1, b :: l2 => eqb a b && eqb_list eqb l1 l2
    | _, _ => false
  end.

Lemma eqb_list_true_iff :
  forall A (eqb : A -> A -> bool),
    (forall a1 a2, eqb a1 a2 = true <-> a1 = a2) ->
    forall l1 l2, eqb_list eqb l1 l2 = true <-> l1 = l2.
Proof.
  Admitted.


Fixpoint forallb {X : Type} (test : X -> bool) (l : list X) : bool :=
  match l with
  | [] => true
  | x :: l' => andb (test x) (forallb test l')
  end.

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
Admitted.


Theorem forallb_true_iff : forall X test (l : list X),
   forallb test l = true <-> All (fun x => test x = true) l.
Proof.
Admitted.


(*********************************)

Notation var := string.
Definition var_eq : forall x y : var, {x = y} + {x <> y} := string_dec.

Infix "==v" := var_eq (no associativity, at level 50).

Inductive arith : Set :=
| Const (n : nat)
| Var (x : var)
| Plus (e1 e2 : arith)
| Minus (e1 e2 : arith)
| Times (e1 e2 : arith).

(* A valuation represents a mapping between variables and their values *)

(* Valuations are implemented as partial maps - see *)
(*     https://softwarefoundations.cis.upenn.edu/lf-current/Maps.html *)
(* for an explanation of how partial maps are defined *)

(* You'll need to compile Maps.v and make sure the compiled file is in the *)
(* same directory (or in a path Coq knows about) as this file *)

Definition valuation := partial_map nat.

Fixpoint interp (e : arith) (m : valuation) : nat :=
    match e with
  | Const n => n
  | Var x  =>
    match (m x)  with
    | None => 0 (* goofy default value! *)
    | Some n => n
    end
  | Plus e1 e2 => interp e1 m + interp e2 m
  | Minus e1 e2 => interp e1 m - interp e2 m
  | Times e1 e2 => interp e1 m * interp e2 m
  end.

(* Here's a simple transformation. *)
Fixpoint commuter (e : arith) : arith :=
  match e with
  | Const _ => e
  | Var _ => e
  | Plus e1 e2 => Plus (commuter e2) (commuter e1)
  | Minus e1 e2 => Minus (commuter e1) (commuter e2)
                   (* ^-- NB: didn't change the operand order here! *)
  | Times e1 e2 => Times (commuter e2) (commuter e1)
  end.

Theorem commuter_ok : forall v e, interp (commuter e) v = interp e v.
Proof.
  Admitted.

(* Next, we will consider compiling this language to a simple
   stack machine which supports the following instructions *) 

Inductive instruction :=
| PushConst (n : nat)
| PushVar (x : var)
| Add
| Subtract
| Multiply.

(* The behavior of the machine is straightforward: binary arithmetic 
 * operations pop their arguments off the stack, compute the result, and 
 * return a new stack with this result at the top.  *)

(* The run1 function computes how to execute a single instruction given a 
 * mapping of variables to values (v) and a stack (represented as a list of numbers) *)

Definition run1 (i : instruction) (v : valuation) (stack : list nat) : list nat :=
  match i with
  | PushConst n => n :: stack
  | PushVar x => (match (v x) with
                  | None => 0
                  | Some n => n
                  end) :: stack
  | Add =>
    match stack with
    | arg2 :: arg1 :: stack' => arg1 + arg2 :: stack'
    | _ => stack (* arbitrary behavior in erroneous case (stack underflow) *)
    end
  | Subtract =>
    match stack with
    | arg2 :: arg1 :: stack' => arg1 - arg2 :: stack'
    | _ => stack (* arbitrary behavior in erroneous case *)
    end
  | Multiply =>
    match stack with
    | arg2 :: arg1 :: stack' => arg1 * arg2 :: stack'
    | _ => stack (* arbitrary behavior in erroneous case *)
    end
  end.

(* Here's how to run several instructions. *)
Fixpoint run (is : list instruction) (v : valuation) (stack : list nat) : list nat :=
  match is with
  | nil => stack
  | i :: is' => run is' v (run1 i v stack)
  end.

(* Now, we can directly compile an arithmetic expression to an equivalent stack program *)
Fixpoint compile (e : arith) : list instruction.
  Admitted.

(* Finally, we would like to prove that the values produced by interpreting arithmetic 
 * expressions are the same as the result of compiling these expressions to the stack   
 * machine and running the compiled version.                                           *)

(* Here is a useful lemma that will help the proof. *)
Lemma compile_ok' : forall e v is stack, run (compile e ++ is) v stack = run is v (interp e v :: stack).
Proof.
  Admitted.


(* The overall theorem follows as a simple corollary. *)
Theorem compile_ok : forall e v, run (compile e) v nil = interp e v :: nil.
Proof.
  Admitted.
