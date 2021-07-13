
(* Correctness proof of a (very) simple compiler *)

(* The purpose of this exercise is to use Coq to verify the              *)
(* correctness of a simple compiler. The source language is a single     *)
(* expression involving integer constants, variables and addition. The   *) 
(* target language is a assembly-like language with a single accumulator *)
(* and an infinite set of registers.                                     *)        

Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Omega.
Require Import Coq.Arith.EqNat.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Logic.FunctionalExtensionality.

Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.

Open Scope string_scope. Open Scope nat_scope.


(* The following introduces useful notations and a number of helpful  *)
(* auxiliary functions.                                               *)

Notation "x :: y" := (cons x y) (at level 60, right associativity).
Notation "[]" := nil.
Notation "[ x ]" := (cons x nil).
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).
Notation "| A |" := (length A) (at level 70).
Notation "x ++ y" := (app x y) (at level 60, right associativity).


Inductive Id :=
  id : nat -> Id.

Definition beq_id x y :=
  match x,y with
  | (id n1), (id n2) => if (n1 =? n2)  then true else false
  end.

Theorem beq_id_refl : forall id, true = beq_id id id.
Proof.
  intros. simpl. unfold beq_id. destruct id0.  destruct (n =? n) eqn: H.
  - reflexivity.
  - rewrite <- H. destruct n. reflexivity.
    simpl in H.  rewrite Nat.eqb_refl in H. discriminate H.
Qed.

Theorem beq_id_true_iff : forall x y : Id,
  beq_id x y = true <-> x = y.
Proof.
  Admitted.

Theorem beq_id_false_iff : forall x y : Id,
  beq_id x y = false
  <-> x <> y.
Proof.
  Admitted.

Theorem false_beq_id : forall x y : Id,
   x <> y
   -> beq_id x y = false.
Proof.
  Admitted.

(* Registers are denoted as numbers *)

Definition reg := nat.

(* Elements of the target memory (called cells) are either Registers            *)
(* (of which there are) an infinite number, or an Accumulator which is unique.  *)

Inductive cell : Set := (* memory cells *)
| Reg : reg -> cell
| Acc : cell.

(* The following are some useful definitions and properties about cells. *)

Definition cell_id x y :=
  match x,y with
    | Acc, Acc => true
    | (Reg r1), (Reg r2) => beq_id (id r1) (id r2)
    | _,_ => false                                    
  end.

Theorem cell_refl : forall c, true = cell_id c c.
Proof.
  intros. simpl. unfold cell_id. destruct c.
  + simpl. destruct (r =? r) eqn: H. reflexivity. rewrite Nat.eqb_refl in H. discriminate.
  + reflexivity.
Qed.

  
Theorem cell_true_iff : forall x y : cell,
  cell_id x y = true <-> x = y.
Proof.
Admitted.

Theorem cell_false_iff : forall x y : cell,
  cell_id x y = false
  <-> x <> y.
Proof.
  intros x y. rewrite <- cell_true_iff.
  rewrite not_true_iff_false. reflexivity. Qed.

Theorem false_beq_cell : forall x y : cell,
   x <> y
   -> cell_id x y = false.
Proof.
  intros x y. rewrite cell_false_iff.
  intros H. apply H. Qed.


(* We relate cells to the values they hold using maps *)

Definition total_map (A: Type) (B: Type) := A -> B.

Definition t_empty {A:Type} {B:Type} (v : B) : total_map A B :=
  (fun _ => v): A -> B.

Definition total_cell_map (A:Type) := total_map cell A.

Definition t_update {A:Type} (m : total_cell_map A)
                    (x : cell) (v : A) :=
  fun x' => match (x,x') with
           | (Acc,Acc) => v
           | ((Reg n1), (Reg n2)) => if beq_id (id n1) (id n2) then v else m x'
           | (_,_) => m x'
         end.

Lemma t_apply_empty:  forall A B x v, @t_empty A B v x = v.
Proof.
  reflexivity.
Qed.

Lemma t_update_eq : forall A (m: total_cell_map A) x v,
  (t_update m x v) x = v.
Proof.
  Admitted.
  
Lemma t_update_neq : forall (X:Type) v x1 x2
                         (m : total_cell_map X),
  x1 <> x2 ->
  (t_update m x1 v) x2 = m x2.
Proof.
  Admitted.

Lemma t_update_shadow : forall {A : Type} (s: total_cell_map A) v1 v2 x,
    t_update (t_update s x v1) x v2
  = t_update s x v2.
Proof.
  (* Hint: You might need to use functional_extensionality *)
  Admitted.

(* -------------------------------------------------------------------------- *)
(* The syntax of the source language.  An expression is either a constant,    *)
(* a "bind" expression that binds an identifier to a value, and evaluates an  *)
(* expression in the context of that binding, an addition operation, and a    *)
(* derf constructor that returns the value of its identifier                  *)

Inductive expr : Set :=
|const : nat -> expr
|bind : Id -> expr -> expr -> expr
|add : expr -> expr -> expr
|deref : Id -> expr.

(* The semantics of the source language *)

(* The state is an environment that maps identifiers to values - *)
(* in this language all values are numbers                       *)

Definition state := total_map Id  nat.
    
Definition empty_state := @t_empty Id nat 0.

Definition state_update (st : state) (x : Id) (v : nat) :=
  fun x' =>  if beq_id x x' then v else st x'.

Lemma state_update_eq : forall (st: state) x v,
  (state_update st x v) x = v.
Proof.
  intros. unfold t_update. destruct x. unfold state_update.
  rewrite <- beq_id_refl. reflexivity.
Qed.  


Lemma state_update_neq : forall v x1 x2 (st : state),
  x1 <> x2 ->
  (state_update st x1 v) x2 = st x2.
Proof.
  Admitted.

(* E is an interpreter for our source language - given a state   *)
(* and an expression, it returns the result of evaluating the    *)
(* expression in the context of that state.                      *)

Fixpoint E (s : state) (e : expr) {struct e} : nat  :=
match e with
  |const n => n
  |deref x => (s x)
  |bind x e1 e2 => E (fun y => if (beq_id x y) then (E s e1) else (s y)) e2
  |add e1 e2 => match (E s e1) with
                 | v1 => match (E s e2) with
                                | v2 => v1+v2
                             end
               end
end.

(* ----------------------------------------------------------------- *)
(* The target language manipulates an infinite set of registers and  *)
(* the accumulator                                                   *)

(* Specifically, 
   -  LI n loads the immediate value n in the accumulator;
   -  LOAD r loads the contents of register r in the accumulator; 
   -  STO r stores the contents of the accumulator in register r; 
   -  ADD r adds the contents of register r to the accumulator.
*)

Inductive instr : Set :=
|LI : nat -> instr
|LOAD : reg -> instr
|STO : reg -> instr
|ADD : reg -> instr
.

(* semantics of the target language *)

Definition store := total_map cell nat.

Definition update (s : store) (c : cell) (v : nat) :=
  t_update s c v.
    
Definition empty_store := @t_empty cell nat 0.

Definition store_lookup (s : store) (c : cell) := (s c).

(* Si defines an interpreter for target instructions, returning *)
(* a new store after the instruction has been evaluated in the  *)
(* context of the store argument provided.                      *)

Definition Si (s : store) (i : instr) : store :=
match i with
  |LI n => update s Acc n
  |LOAD r => update s Acc (store_lookup s (Reg r))
  (* fill in the cases for STO and ADD *)                   
  |STO r => s
  |ADD r => s
end.

(* Sl generalizes Si to operate over a list of instructions  *)
Fixpoint Sl (s : store) (l : list instr) {struct l} : store .
Admitted.

(* -------------------------------------------------------------- *)
(* the compiler *)

(* A symbol table is a map that relates identifiers and registers *)

Definition symt := total_map Id reg.

Definition empty_symt := @t_empty Id reg 0 .

Definition symt_update (m : symt) (x : Id) (r : reg) :=
  fun (x' : Id) => if beq_id x x' then r else m x'.

Definition symt_lookup (m : symt) (x : Id) := (m x).

Lemma symt_update_eq : forall (m: symt) x r,
  symt_update m x r x = r.
Proof.
  Admitted.


Lemma symt_update_neq : forall v x1 x2 (m : symt),
  x1 <> x2 ->
  (symt_update m x1 v) x2 = m x2.
Proof.
  Admitted.



(* Let e be an expression and m an assignment from its variables
   to registers. Assume r to be a register  whose id is greater 
   than those used in m for the variables of e. Then the compilation 
   of e is a list of instructions that satisfies the inductive
   proposition C(m,r,e,l) defined as follows:    *)

(*     C(m r (const n) [LI n])                                  *)
(*     C(m r (deref x) [LOAD m x]                               *)
(*     C(m r (bind x e1 e2) [l1 ++ [STO r] ++ l2]) where        *)
(*            C(m r e1 l1) and C(m[x -> r] (r+1) e2 l2) hold    *)
(*     C(m r (add e1 e2) [l1 ++ [STO r] ++ l2 ++ [ADD r] where  *)
(*            C(m r e1 l1) and C(m (r+1) e2 l2)                 *)

(* When this list of instructions is executed, it stops with    *)
(*   the value of e in the accumulator.                         *)

Inductive C : symt -> reg -> expr -> list instr -> Prop :=
  |c_const (m : symt) (r : reg) (e : expr) (l : list instr) (n : nat) :
      (C m r (const n) [LI n])
  |c_deref (m: symt) (r : reg) (e : expr) (l : list instr) (x : Id) :
      (C m r (deref x) [LOAD (m x)]).
(* Fill in the cases for bind and add *)


(* ------------------------------------------------------------ *)
(* The main theorems                                            *)

Lemma Sl_append :
 forall (l1 l2 : list instr) (s : store), Sl s (l1 ++ l2) = Sl (Sl s l1) l2.
Proof.
  Admitted.

Lemma Sl_invariant :
  forall (e : expr) (m : symt) (s : store) (r r' : reg) (l : list instr),
     r' < r  -> 
     (C m r e l) ->
     Sl s l (Reg r')  = s (Reg r').
Proof.
  Admitted.

Theorem correctness :
  forall (e : expr) (m : symt) (r : reg) (l : list instr) (s : store) (st: state),
    (C m r e l) ->
    (forall (v : Id), (m v) < r) ->
    (forall (v : Id), st v = s (Reg (m v))) ->  Sl s l Acc = E st e.
Proof.
  Admitted.
     