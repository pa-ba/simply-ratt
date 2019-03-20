From Coq Require Import Program.Equality Omega.
From SimplyRatt Require Export Streams FundamentalProperty.

From SimplyRatt Require Import Tactics.

Import ListNotations.

Theorem causality1 A B k t :
  vtype A ->
  ctx_empty ⊢ t ∶ Box (Arrow (Str A) (Str B)) ->
  trrel A B k (app (unbox t) (adv (ref thel)),heap_empty).
Proof.
  intros VTA Ty. constructor; eauto using closed_heap_empty, typed_closed, heap_empty_fresh.
  intros v w V W.
  assert (ctx_lock ctx_empty ⊢ unbox t ∶ Arrow (Str A) (Str B)) as Ty' by eauto.
  eapply fund_prop with (g:= nil) (Hs := (str_heapseq A k))
                        (s := store_lock (Some (heap_single thel (v ∷ ref thel)))
                                         (heap_single thel (w ∷ ref thel)))
    in Ty';eauto. rewrite sub_empty_app in Ty' by auto. eapply trel_app;
  eauto using typed_closed. eapply trel_adv. auto using mapsto_heap_cons.
  apply vrel_trel. autorewrite with vrel. eexists. split. reflexivity. simpl.
  autorewrite with vrel. do 2 eexists. split. reflexivity. split.
  rewrite vtype_tsubst by auto. eauto using vtype_vrel.
  eapply vrel_mono; try eapply thel_vrel;eauto.
  eapply crel_lock;eauto using str_heapseq_closed.
  eauto using str_heapseq_closed.
  constructor;  eauto using vtype_vrel_closed,closed_heap_alloc, closed_heap_empty.
Qed.

Theorem causality2 A B k s v :
  vtype A -> isvalue v -> ctx_empty ⊢ v ∶ A -> 
  trrel A B (S k) s -> exists v' s', tred s v v' s' /\ trrel A B k s'.
Proof.
  intros VTA V Ty TR. inversion TR;subst.
  apply typing_vtype with (Hs:=[]) (s:=store_bot) in Ty; eauto.
  pose (vtype_inhab _ VTA) as W. destruct W as (w&W).
  assert (exists (v' : term) (s : store),
  {t, (store_lock (Some (heap_cons h thel (v ∷ ref thel))) (heap_single thel (w ∷ ref thel)))}⇓ {v', s} /\
  vrel Str (B) (str_heapseq (A) (S k)) s v') as Red.
  eapply H1 with (v:=v); try eassumption;eauto using tick_le_refl,str_heapseq_closed.
  constructor; eauto using vtype_vrel_closed,closed_heap_alloc,closed_heap_empty.

  destruct Red as (v'& s&R&VR).
  
  pose (red_extensive _ _ _ _ R) as SL. dependent destruction SL. 
  eapply red_not_later with (u:=unit) in R; eauto using heap_dom_cons'.
  rewrite heap_cons_eq in R.
  autorewrite with vrel in VR. simpl in VR. destruct VR as (v'' & E & VR). subst.
  autorewrite with vrel in VR. simpl in VR. destruct VR as (v1 & v2 & E & VR). subst.
  
  do 2 eexists. split. econstructor. apply R. constructor.
  - assert (heap_mapsto thel (w ∷ ref thel) h2') by eauto using mapsto_heap_cons.
    assert (closed_term (w ∷ ref thel)) by eauto using vtype_vrel_closed.
    assert (closed_heap (heap_cons h2' thel unit)). apply red_closed in R;eauto.
    destruct R as [C1 C2]. inversion C2. auto.
    constructor;eauto using closed_heap_empty,closed_heap_alloc,vtype_vrel_closed.
    eauto using closed_heap_cons_rev.
  - destruct VR; eauto using vrel_delay_closed. 
  - intros. 

    assert (exists (v' : term) (s : store),
               {t, (store_lock (Some (heap_cons h thel (v ∷ ref thel))) (heap_single thel (v0 ∷ ref thel)))}⇓ {v', s} /\
               vrel Str (B) (str_heapseq (A) (S k)) s v') as Red2.

    eapply H1 with (v:=v) (w:=v0); try eassumption;eauto using tick_le_refl,str_heapseq_closed.
  constructor; eauto using vtype_vrel_closed,closed_heap_alloc,closed_heap_empty.
  
  destruct Red2 as (v'& s&R'&VR').

  pose (red_extensive _ _ _ _ R') as SL. dependent destruction SL. 
  eapply red_not_later with (u:=unit) in R'; eauto using heap_dom_cons'.
  rewrite heap_cons_eq in R'.

  pose (red_determ _ _ _ _ _ _ R R') as D. destruct D as [E D]. subst.
  dependent destruction D.

  autorewrite with vrel in VR'. simpl in VR'. destruct VR' as (v'' & E & VR'). subst.
  autorewrite with vrel in VR'. simpl in VR'. destruct VR' as (v1' & v2' & E' & VR1 & VR2). subst.
  dependent destruction E.
  autorewrite with vrel in VR2.  autodest. simpl in H11.
  assert (heap_cons h2' thel (v0 ∷ ref thel) = h2'0) as HR by
        (eapply heap_overwrite; eauto using mapsto_heap_cons). 
  rewrite HR.
  dependent destruction H9. eapply trel_adv;eauto.
  eapply H10. constructor. eauto using vtype_vrel_closed. assumption. 
Qed.