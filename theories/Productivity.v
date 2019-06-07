(** This module proves that the stream semantics defined in module
[Streams] is safe (cf. Theorem 3.1 in the paper). In particular, we
prove Lemma 6.6, from which Theorem 3.1 follows. *)

From SimplyRatt Require Export Streams FundamentalProperty.

From Coq Require Import Program.Equality.

(** This is part (i) of Lemma 6.6 in the paper. *)
Theorem productivity1 A k t : ctx_empty ⊢ t ∶ Box (Str A) -> strel A k (unbox t,heap_empty).
Proof.
  intros T. assert (ctx_lock ctx_empty ⊢ unbox t ∶ Str A) as T' by auto.
  constructor; eauto using closed_heap_empty, typed_closed. 
  eapply fund_prop with (g := nil) (Hs := empty_heaps k)
                        (s := store_lock (Some heap_empty) heap_empty) in T';
    try rewrite sub_empty_app in *;eauto using empty_heaps_closed, closed_heap_empty.
Qed.

(** This is part (ii) of Lemma 6.6 in the paper. *)
Theorem productivity2 A k s : vtype A -> strel A (S k) s -> exists s' v, ctx_empty ⊢ v ∶ A  /\ sred s v s' /\ strel A k s'.
  intros VT SR. destruct SR as [t h CH CT TR].
  assert (exists v s'', {t, store_lock (Some h) heap_empty}⇓ {v, s''} /\ vrel Str A (empty_heaps (S k)) s'' v) as RV.
  apply TR;eauto using empty_heaps_closed, closed_heap_empty.
  destruct RV as (v' & s'' & R & V).
  assert (closed_store s'') as CS.
  eapply red_closed;try eassumption;eauto using closed_heap_empty.
  pose (red_extensive _ _ _ _ R) as RL.
  inversion RL. subst.
  inversion CS. subst.
  
  autorewrite with vrel in *. simpl in V. rewrite vtype_tsubst in V by assumption.
  destruct V as (v'' & E & V). subst. autorewrite with vrel in *. simpl in V.
  destruct V as (v & v''' & E & V1 & V2);subst.
  autorewrite with vrel in *. simpl in V2.
  destruct V2 as (l & u & E & M & TR');subst.


  eexists. eexists. 
  split. eapply vtype_typing; eassumption.

  split.
  econstructor. apply R.

  constructor;eauto. dependent destruction M. eapply trel_adv. eauto.
  unfold trel in *. intros.
  eapply TR';eauto using empty_heaps_closed, closed_heap_empty.                                     
Qed.