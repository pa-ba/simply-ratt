(** This module defines the type system of Simply RaTT. *)

From SimplyRatt Require Export Substitutions.

From Coq Require Import Omega Program.Equality.

(* Definition of well-formed types *)
Inductive wf_type : nat -> type -> Prop :=
| IT_Unit : forall Th,
    wf_type Th Unit
| IT_Nat  : forall Th,
    wf_type Th Nat
| IT_TypeVar : forall Th i,
    i < Th ->
    wf_type Th (TypeVar i)
| IT_Times : forall Th T1 T2,
    wf_type Th T1 ->
    wf_type Th T2 ->
    wf_type Th (Times T1 T2)
| IT_Plus : forall Th T1 T2,
    wf_type Th T1 ->
    wf_type Th T2 ->
    wf_type Th (Plus T1 T2)
| IT_Arrow : forall Th T1 T2,
    wf_type Th T1 ->
    wf_type Th T2 ->
    wf_type Th (Arrow T1 T2)
| IT_Delay : forall Th T,
    wf_type Th T ->
    wf_type Th (Delay T)
| IT_Box : forall Th T,
    wf_type Th T ->
    wf_type Th (Box T)
| IT_Mu : forall Th T,
    wf_type (S Th) T ->
    wf_type Th (Mu T).

(* A closed type is well-formed in the empty context *)
Definition closed_type (T : type) : Prop := wf_type 0 T.


(* Definition of stable types *)
Inductive stable : type -> Prop :=
| S_Unit : stable Unit
| S_Nat : stable Nat
| S_Times : forall T1 T2,
    stable T1 ->
    stable T2 ->
    stable (Times T1 T2)
| S_Plus : forall T1 T2,
    stable T1 ->
    stable T2 ->
    stable (Plus T1 T2)
| S_Box : forall T,
    stable (Box T).

Inductive ctype := init | now | later.

Inductive ctx : ctype -> Set := 
| ctx_empty : ctx init
| ctx_var {ty} : ctx ty -> type -> ctx ty
| ctx_skip {ty} : ctx ty -> ctx ty
| ctx_lock : ctx init -> ctx now
| ctx_tick : ctx now -> ctx later.



Fixpoint skip_later (G : ctx later) : ctx now :=
  match G with
  | ctx_tick G' => G'
  | @ctx_var later G' _ => ctx_skip (skip_later G')
  | @ctx_skip later G' => ctx_skip (skip_later G')
  end.


Fixpoint skip_now (G : ctx now) : ctx init :=
  match G with
  | ctx_lock G' => G'
  | @ctx_var now G' _ => ctx_skip (skip_now G')
  | @ctx_skip now G' => ctx_skip (skip_now G')
  end.

Inductive ctx_lookup {ty} : ctx ty -> nat -> type -> Prop :=
| ctx_zero G T : ctx_lookup (ctx_var G T) 0 T
| ctx_succ G T T' n : ctx_lookup G n T -> ctx_lookup (ctx_var G T') (S n) T
| ctx_succ_skip G T  n : ctx_lookup G n T -> ctx_lookup (ctx_skip G ) (S n) T.


Reserved Notation "G '⊢' e '∶' T" (at level 40). 
Inductive hastype : forall {ty}, ctx ty -> term -> type -> Prop :=
(* Simple λ-calculus with sums and products *)
| T_unit : forall ty (G : ctx ty),
    G ⊢ unit ∶ Unit
| T_nat : forall ty (G : ctx ty) n,
    G ⊢ natlit n ∶ Nat
| T_var : forall ty (G : ctx ty) x T,
    ctx_lookup G x T ->
    G ⊢ var x ∶ T
| T_abs : forall ty (G : ctx ty) t T1 T2,
    ty <> later ->
    ctx_var G T1 ⊢ t ∶ T2 ->
    G ⊢ abs t ∶ (Arrow T1 T2)
| T_app : forall ty (G : ctx ty) t1 t2 T1 T2,
    G ⊢ t1 ∶ (Arrow T1 T2) ->
    G ⊢ t2 ∶ T1 ->
    G ⊢ app t1 t2 ∶ T2
| T_pair : forall ty (G : ctx ty) t1 t2 T1 T2,
    G ⊢ t1 ∶ T1 ->
    G ⊢ t2 ∶ T2 ->
    G ⊢ pair t1 t2 ∶ (Times T1 T2)
| T_pr1 : forall ty (G : ctx ty) t T1 T2,
    G ⊢ t ∶ (Times T1 T2) ->
    G ⊢ pr1 t ∶ T1
| T_pr2 : forall ty (G : ctx ty) t T1 T2,
    G ⊢ t ∶ (Times T1 T2) ->
    G ⊢ pr2 t ∶ T2
| T_in1 : forall ty (G : ctx ty) t T1 T2,
    G ⊢ t ∶ T1 ->
    G ⊢ in1 t ∶ (Plus T1 T2)
| T_in2 : forall ty (G : ctx ty) t T1 T2,
    G ⊢ t ∶ T2 ->
    G ⊢ in2 t ∶ (Plus T1 T2)
| T_case : forall ty (G : ctx ty) t t1 t2 T T1 T2,
    G ⊢ t ∶ (Plus T1 T2) ->
    ctx_var G T1 ⊢ t1 ∶ T ->
    ctx_var G T2 ⊢ t2 ∶ T ->
    G ⊢ case t t1 t2 ∶ T
(* Reactive expressions *)
| T_delay : forall G T t,
    ctx_tick G ⊢ t ∶ T ->
    G  ⊢ delay t ∶ Delay T
| T_adv : forall G t T ,
    skip_later G ⊢ t ∶ Delay T ->
    G ⊢ adv t ∶ T
| T_progr : forall G t T ,
    stable T -> 
    skip_later G ⊢ t ∶ T ->
    G ⊢ progr t ∶ T
| T_box : forall G t T,
    ctx_lock G ⊢ t ∶ T ->
    G ⊢ box t ∶ (Box T)
| T_unbox : forall G t T,
    skip_now G ⊢ t ∶ Box T ->
    G ⊢ unbox t ∶ T
| T_promote_now : forall G t T,
    stable T ->
    skip_now G ⊢ t ∶ T ->
    G ⊢ promote t ∶ T
| T_promote_later : forall G t T,
    stable T ->
    skip_now (skip_later G) ⊢ t ∶ T ->
    G ⊢ promote t ∶ T
(* Temporal recursive expressions *)
| T_fix : forall G t T,
    (ctx_var (ctx_lock G) (Delay T)) ⊢ t ∶ T ->
    G ⊢ fixp t ∶ Box T
| T_into : forall ty (G : ctx ty) t T,
    G ⊢ t ∶ tsubst 0 T (Delay (Mu T)) ->
    G ⊢ into t ∶ Mu T
| T_out : forall ty (G : ctx ty) t A B,
    B = tsubst 0 A (Delay (Mu A)) ->
    G ⊢ t ∶ Mu A ->
    G ⊢ out t ∶ B
 where "G '⊢' e '∶' T" := (hastype G e T) : type_scope.


Hint Constructors ctx_lookup hastype wf_type.

Hint Unfold closed_type.
