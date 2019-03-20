(* Here we define the operational semantics for streams and stream
transducers. In addition we provide lemmas to prove productivity and
causality. *)


From Coq Require Import Omega Program.Equality.
From SimplyRatt Require Import Tactics.
From SimplyRatt Require Export LogicalRelationAux.


Open Scope type.


Notation "'Str' x" := (Mu (Times x (TypeVar 0))) (at level 0).

Notation "x ∷ y" := (into (pair x y))  (at level 100).

Notation "'head' x" := (pr1 (out x)) (at level 0).

Notation "'tail' x" := (pr2 (out x)) (at level 0).

(* state for the stream reduction semantics *)
Definition state := term * heap.


(* reduction semantics for streams *)
Inductive sred : state -> term -> state -> Prop :=
  sred_step t h v l hn hl :
    red t (store_lock (Some h) heap_empty) (v ∷ l) (store_lock (Some hn) hl) ->
    sred (t, h) v (adv l, hl).


Notation empty_heaps := (repeat (heaps_single heap_empty)).
  

(* Logical relation on streams *)

Inductive strel (A : type) (k : nat) : state -> Prop :=
  strel_intro t h :
    closed_heap h -> closed_term t ->
    trel (Str A) (empty_heaps k) (store_lock (Some h) heap_empty) t ->
    strel A k (t,h).



Lemma empty_heaps_closed k : closed_heapseq (empty_heaps k).
Proof.
  induction k;simpl;eauto. constructor;eauto.
  intros h H. inversion H. subst. apply closed_heap_empty.
Qed. 



Definition thel : loc := 0.

Notation heap_single := (heap_cons heap_empty).

(* reduction semantics for stream transducers *)
Inductive tred : state -> term -> term -> state -> Prop :=
  tred_step t h v v' l hn hl :
    red t (store_lock (Some (heap_cons h thel (v ∷ ref thel))) (heap_single thel unit) )
        (v' ∷ l) (store_lock (Some hn) (heap_cons hl thel unit)) ->
    tred (t, h) v v' (adv l, hl).



Inductive str_heaps (A : type) : heaps :=
  mk_str_heaps v : closed_term v -> vrel A nil store_bot v -> str_heaps A (heap_single thel (v ∷ ref thel)).

Lemma str_heaps_closed A : closed_heaps (str_heaps A).
Proof.
  intros h H. inversion H. subst. eauto using closed_heap_alloc, closed_heap_empty.
Qed. 

Notation "'str_heapseq' A" := (repeat (str_heaps A)) (at level 0).

Lemma str_heapseq_closed A k :  closed_heapseq (str_heapseq A k).
Proof.
  induction k; simpl; eauto using str_heaps_closed.
Qed.


(* Logical relation on stream transducers *)

Inductive trrel (A B : type) (k : nat) : state -> Prop :=
  trrel_intro t h : 
    closed_heap h -> closed_term t -> 
    (forall v w, vrel A nil store_bot v ->
                 vrel A nil store_bot w ->
                 trel (Str B) (str_heapseq A k)
                      (store_lock (Some (heap_cons h thel (v ∷ ref thel)))
                                  (heap_single thel (w ∷ ref thel))) t) ->
    trrel A B k (t,h).


Lemma red_lock  t hn hl v h l :
  heap_dom l hl -> 
  {t, store_lock hn hl} ⇓ {v, h} ->
  exists hn' hl', h = store_lock hn' hl' /\ heap_dom l hl'.
Proof.
  intros I R. apply red_extensive in R. inversion R;subst;
  eexists; eexists; split;eauto using heap_le_dom.
Qed.

Ltac red_lock := match goal with
                 | [ H : red _ (store_lock _ ?hl) _ _ , I : heap_dom _ ?hl |- _] =>
                   eapply red_lock in H;auto;autodest;red_lock
                 | _ => eauto
                 end.

Lemma red_not_later hn hl hn' hl' l t u v :
  heap_dom l hl ->
  {t,store_lock hn hl} ⇓ {v,store_lock hn' hl'} ->
  {t,store_lock hn (heap_cons hl l u)} ⇓ {v,store_lock hn' (heap_cons hl' l u)}.
Proof.
  intros I R. dependent induction R;eauto;try solve[red_lock].
  - pose (red_delay t (heap_cons hl l u) hn') as R. rewrite alloc_dom in R by assumption.
    rewrite heap_cons_comm in R by (apply heap_dom_alloc_fresh;auto).
    apply R.
  - eapply red_unbox_fix. eassumption. rewrite alloc_dom by assumption.
    rewrite heap_cons_comm by (apply heap_dom_alloc_fresh;auto).
    apply IHR2; auto using heap_dom_cons. 
Qed.

Lemma thel_vrel v A k :
  vtype A -> vrel A nil store_bot v ->
  vrel (Delay (Str A)) (str_heapseq A k)
                  (store_lock None (heap_single thel (v ∷ ref thel))) (ref thel).
Proof.
  intros VT VR. generalize dependent v. induction k;intros.
  - rewrite vrel_delay_nil. eauto.
  - simpl. rewrite vrel_delay. exists thel. exists (v ∷ ref thel).
    split. reflexivity. split. eauto using mapsto_heap_cons.
    intros. apply vrel_trel. rewrite vrel_mu. eexists. split.
    reflexivity. simpl. rewrite vrel_times. do 2 eexists. split. reflexivity.
    split. rewrite vtype_tsubst by auto. eauto using vtype_vrel.
    inversion H. subst.
    eapply vrel_mono with (s := (store_lock None (heap_single thel (v0 ∷ ref thel))));eauto.
Qed.

