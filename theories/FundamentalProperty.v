(** This module proves the fundamental property of the logical
relation defined in the [LogicalRelation] module. *)

From SimplyRatt Require Import Tactics.

From SimplyRatt Require Export LogicalRelationAux.

From Coq Require Import Program.Equality Arith.Wf_nat Omega.


Lemma vrel_box_cases A Hs Hs' s v h h' :
  vrel (Box A) Hs s v -> suffix Hs' Hs -> closed_heapseq Hs' ->
  closed_store (store_lock h h') ->
  (exists t v' s' , v = box t /\   {t,store_lock h h' } ⇓ {v',s'} /\ vrel A Hs' s' v')
  \/ (exists t v' s',
         v = fixp t /\ 
         {sub_term t (ref (alloc_fresh h')) ,store_lock h (heap_cons h' (alloc_fresh h') (unbox (fixp t))) } ⇓ {v',s'} /\
         vrel A Hs' s' v').
Proof.
  intros V Su Cl CS. rewrite vrel_box in V. unfold trel in V.
  destruct V as [Va T].

  pose (T _ Su _ _ (heapseq_le_refl _) (tick_le_empty h h') Cl CS) as T'.
  destruct T' as (w & s'& R & V').
  inversion R.
  + inversion H.
  + inversion H0; subst;try solve[inversion Va]. left.
    do 3 eexists. repeat split; eauto.
  + subst. inversion H2; subst;try solve[inversion Va]. right.
    do 5 eexists. repeat split;eauto using heap_fresh_alloc. auto.
Qed.

(** Fundamental property (cf. Theorem 6.3 in the paper). *)

Theorem fund_prop ty (G : ctx ty) t A Hs s g :
  hastype G t A -> crel G Hs s g -> closed_sub g ->
  closed_heapseq Hs -> closed_store s ->
  trel A Hs s (sub_app g t).
Proof.
  intros T. generalize dependent g. generalize dependent Hs.
  generalize dependent s. 
  induction T;  intros s Hs g C CS CH Cs.
  - (* unit *)
    apply vrel_trel. simpl. autorewrite with vrel. auto.
  - (* natlit *)
    apply vrel_trel. simpl. autorewrite with vrel. eauto.
  - (* var *)
    eapply ctx_lookup_vrel in H; try eassumption. autodest.
    apply vrel_trel. simpl. rewrite H. assumption.
  - (* abs *)
    apply vrel_trel. simpl. autorewrite with vrel.
    exists (sub_app (None :: g) t). split. reflexivity.
    intros. rewrite sub_term_merge.
    apply IHT. constructor. assumption.
    apply crel_gc in C. eauto using crel_mono. assumption.
    auto. auto. auto. auto.
  - (* app *)
    unfold trel in *. intros Hs' s' HS TL HCH HCs.
    pose (IHT1 _ _ _ C CS CH Cs _ _ HS TL HCH HCs) as IH1.
    destruct IH1 as (v & s''& [IH1s IH1v]).
    rewrite vrel_arrow in IH1v.
    destruct IH1v as (u & [V IH1]). subst.
    assert (tick_le s s'') as TL' by eauto using tick_le_trans, red_extensive.
    assert (closed_term (abs u) /\ closed_store s'') as HCC
        by (apply red_closed with (t := sub_app g t1) (s := s');eauto using crel_sub_closed).
    destruct HCC as [HC'' HCs'].
    pose (IHT2 _ _ _ C CS CH Cs _ _ HS TL' HCH HCs') as IH2.
    destruct IH2 as (v' & s'''& [IH2s IH2v]).
    apply vrel_gc in IH2v.
    assert (store_le (gc s'') (gc s''')) as SL by
          eauto using tick_le_gc,red_extensive.
    assert (closed_term v' /\ closed_store s''') as CT by
          (apply red_closed with (t := sub_app g t2) (s := s'');eauto using crel_sub_closed).
    destruct CT as [CT CTS].
    assert (closed_store (gc s''')) as CGS by (eauto using closed_store_gc).
    pose (IH1 _ (gc s''') (heapseq_le_refl _) SL HCH CGS v' IH2v CT _ _ (heapseq_le_refl _)
              (tick_le_gc' s''') HCH CTS) as IH1v.
    destruct IH1v as (w & s1 & [R V]).
    exists w, s1. simpl. eauto.
  - (* pair *)
    unfold trel in *. intros Hs' s' HS TL HCH HCs.
   
    assert (exists (v : term) (s'' : store),
               {sub_app g t1, s'}⇓ {v, s''} /\ vrel T1 Hs' s'' v) as IH1 by
          (eapply IHT1; eauto).
    destruct IH1 as (v & s'' & R1 & V1).
    assert (closed_term (sub_app g t1)) as CT by eauto using crel_sub_closed.
    pose (red_closed _ _ _ _ CT HCs R1) as MC.
    destruct MC as [CV Cs'].
    pose (red_extensive _ _ _ _ R1) as Ex1.
    apply tick_le_store in Ex1.
    assert (exists (v' : term) (s''' : store),
               {sub_app g t2, s''}⇓ {v', s'''} /\ vrel T2 Hs' s''' v') as IH2 by
          (eapply IHT2; eauto using tick_le_trans).
    destruct IH2 as (v' & s''' & R2 & V2).

    pose (red_extensive _ _ _ _ R2) as Ex2.
    apply tick_le_store in Ex2.
    eexists. eexists. simpl. split. eapply red_pair;eauto.
    rewrite vrel_times. eexists. eexists.
    split. reflexivity.  eauto using vrel_mono.
  - (* pr1 *)
    unfold trel in *. intros Hs' s' HS TL HCH HCs.
    assert (exists (v : term) (s'' : store),
               {sub_app g t, s'}⇓ {v, s''} /\ vrel (Times T1 T2) Hs' s'' v) as IH by
          (eapply IHT; eauto).
    destruct IH as (v & s'' & R & V).
    rewrite vrel_times in V. autodest.
    eexists. eexists. split. simpl. eapply red_pr1. eassumption. assumption.
     
  - (* pr2 *)
    unfold trel in *. intros Hs' s' HS TL HCH HCs.
    assert (exists (v : term) (s'' : store),
               {sub_app g t, s'}⇓ {v, s''} /\ vrel (Times T1 T2) Hs' s'' v) as IH by
          (eapply IHT; eauto).
    destruct IH as (v & s'' & R & V).
    rewrite vrel_times in V. autodest.
    eexists. eexists. split. simpl. eapply red_pr2. eassumption. assumption.
  - (* in1 *)
    unfold trel in *. intros Hs' s' HS TL HCH HCs.
    assert (exists (v : term) (s'' : store),
               {sub_app g t, s'}⇓ {v, s''} /\ vrel T1 Hs' s'' v) as IH by
          (eapply IHT; eauto).
    destruct IH as (v & s'' & R & V).

    eexists. eexists. split. simpl. eapply red_in1. eassumption.
    rewrite vrel_plus. eauto.
    
  - (* in2 *)
    unfold trel in *. intros Hs' s' HS TL HCH HCs.
    assert (exists (v : term) (s'' : store),
               {sub_app g t, s'}⇓ {v, s''} /\ vrel T2 Hs' s'' v) as IH by
          (eapply IHT; eauto).
    destruct IH as (v & s'' & R & V).

    eexists. eexists. split. simpl. eapply red_in2. eassumption.
    rewrite vrel_plus. eauto.
  - (* case *)
    simpl. unfold trel in *. intros Hs' s' HS TL HCH HCs.
   
    assert (exists (v : term) (s'' : store),
         {sub_app g t, s'}⇓ {v, s''} /\ vrel (Plus T2 T3) Hs' s'' v) as IH1 by
          (eapply IHT1; eauto).
    destruct IH1 as (v & s'' & R1 & V1). clear IHT1.
    assert (closed_term (sub_app g t)) as CT by eauto using crel_sub_closed.
    pose (red_closed _ _ _ _ CT HCs R1) as MC.
    destruct MC as [CV Cs'].
    pose (red_extensive _ _ _ _ R1) as Ex1.
    apply tick_le_store in Ex1.
    rewrite vrel_plus in V1.
    destruct V1 as [V1|V1]; destruct V1 as (v0 & Subst & V1);subst.
    + inversion CV. subst.
      assert (exists (v' : term) (s''' : store),
                 {sub_app (Some v0 :: g) t1, s''}⇓ {v', s'''} /\ vrel T1 Hs' s''' v') as IH2 by
            (eapply IHT2; eauto using tick_le_trans, crel_var,crel_mono).

      destruct IH2 as (v' & s''' & R2 & V2).
          
      pose (red_extensive _ _ _ _ R2) as Ex2.
      apply tick_le_store in Ex2.
    
      eexists. eexists. split. simpl. 
      eapply red_case1; try eassumption. rewrite sub_term_merge. eassumption. assumption.
      assumption.
    + inversion CV. subst.
      assert (exists (v' : term) (s''' : store),
                 {sub_app (Some v0 :: g) t2, s''}⇓ {v', s'''} /\ vrel T1 Hs' s''' v') as IH2 by
            (eapply IHT3; eauto using tick_le_trans, crel_var,crel_mono).

      destruct IH2 as (v' & s''' & R2 & V2).
          
      pose (red_extensive _ _ _ _ R2) as Ex2.
      apply tick_le_store in Ex2.
    
      eexists. eexists. split. simpl. 
      eapply red_case2; try eassumption. rewrite sub_term_merge. eassumption. assumption.
      assumption.
    
  - (* delay *)
    unfold trel. intros Hs' s' HsL TL CHs' Cs'.
    apply crel_mono with (Hs':=Hs') (s':=s') in C;auto.
    assert (exists h h', s' = store_lock h h') as S' by eauto using crel_now'.
    destruct S' as (h&h'&S'). rewrite S' in *.
    eexists. eexists. simpl. split.
    apply red_delay; eauto.
    destruct Hs'.
    + rewrite vrel_delay_nil. eauto.
    + rewrite vrel_delay. eexists. eexists. split. reflexivity.
      split. apply store_mapsto_cons.
      dependent destruction CHs'.
      intros.
      
      apply crel_gc in C;try solve[intro CO;inversion CO].
      
      assert (crel (ctx_tick G) (Hs') (store_lock (Some h') h1) g).
      constructor. eapply crel_mono;try eapply C;eauto.
      constructor; eauto.
      intros h2 HS. inversion HS;subst. exists h1. split;eauto.
      constructor;auto. dependent destruction Cs';eauto.
      assert (closed_term (sub_app g t)).
      eapply crel_sub_closed;eauto.
      
      apply IHT;eauto. constructor. simpl in C.
      eapply crel_mono;try eapply C.
      * constructor;eauto.
        intros h2 HS. inversion HS;subst. exists h1. split;eauto.
      * constructor;auto.
      * eauto using heap_fresh_alloc,heap_cons_mono.
      * dependent destruction Cs';eauto using closed_heap_alloc.
      * simpl. dependent destruction Cs';eauto using closed_heap_alloc.
   - (* adv *)
    unfold trel in *. intros Hs' s' HsL TL CHs' Cs'.
    assert (exists hn hl : heap, s = store_lock (Some hn) hl) as ST by
          eauto using crel_later.
    destruct ST as (hn & hl & ST). subst.
    pose (tick_le_tick' _ _ _ TL) as ST.
    destruct ST as (hn' & hl' & [ST [HLn HLl]]). subst.
    dependent destruction Cs.
    dependent destruction Cs'.
    assert (exists (v : term) (s'' : store),
       {sub_app (sub_skip (skip_later_count G) g) t, store_lock None hn'}⇓ {v, s''} /\
       vrel (Delay T) (heaps_single hl :: Hs') s'' v) as IH by
          (eapply IHT;eauto using crel_skip_later, sub_skip_closed,heaps_single_closed).
    destruct IH as (v & s''& R & V).
    assert (store_le (store_lock None hn') (s'')) as SL
        by eauto using red_extensive.
    inversion SL. subst.
    rewrite vrel_delay in V.
    destruct V as (l & u & [RL [M TT]]). subst.
    assert (closed_term (ref l) /\ closed_store (store_lock None h')) as CL by
          (eapply red_closed; try eassumption;
           eauto using crel_sub_closed, sub_skip_closed, crel_skip_later).
    destruct CL as [CL1 CL2].
    dependent destruction CL2.
    unfold trel in TT.
    assert (exists (v : term) (s'' : store),
               {u, store_lock (Some h') hl'}⇓ {v, s''} /\
               vrel T Hs' s'' v) as TT' by
          (eapply TT ; simpl;eauto using crel_skip_later, sub_skip_closed,heaps_single_closed).
    destruct TT' as (v & s'' & R2 & V2).
    erewrite sub_skip_later_app in R by eauto.
    
    simpl. exists v, s''. split. eapply red_adv. eapply R.
    inversion M;subst. eassumption. eassumption. auto. 

  - (* progress *)
    unfold trel in *. intros Hs' s' HsL TL CHs' Cs'.
    assert (exists hn hl : heap, s = store_lock (Some hn) hl) as ST by
          eauto using crel_later.
    destruct ST as (hn & hl & ST). subst.
    pose (tick_le_tick' _ _ _ TL) as ST.
    destruct ST as (hn' & hl' & [ST [HLn HLl]]). subst.
    dependent destruction Cs.
    dependent destruction Cs'.
    assert (exists (v : term) (s'' : store),
       {sub_app (sub_skip (skip_later_count G) g) t, store_lock None hn'}⇓ {v, s''} /\
       vrel T (heaps_single hl :: Hs') s'' v) as IH by
    (eapply IHT; 
      eauto using crel_skip_later, sub_skip_closed,heaps_single_closed).
    destruct IH as (v & s''& R & V).
    assert (store_le (store_lock None hn') (s'')) as SL
        by eauto using red_extensive.
    inversion SL. subst.
    erewrite sub_skip_later_app in R by eauto. 
    eexists. eexists.
    split. simpl.  apply red_progr.
    eapply R. eapply vrel_stable in V. apply V. auto. auto.
  - (* box *)
    apply vrel_trel. simpl. autorewrite with vrel.
    split. auto. intros Hs0 Su.
    unfold trel in *. intros Hs' s' HsL TL CHs' Cs'.
    assert (exists (v : term) (s'' : store), {sub_app g t, s'}⇓ {v, s''} /\ vrel T Hs' s'' v) as IH.
    eapply IHT; try eassumption;eauto.
    pose (heapseq_le_suffix'' _ _ _ HsL Su CH CHs') as HSS.
    destruct HSS as (Hs'' & HsL' & Su' & CH').
    apply crel_mono with (Hs':=Hs'') (s':=s) in C;eauto.
    eapply crel_lock;try eassumption;eauto.
    rewrite <- tick_le_bot' by apply TL. intros CO;inversion CO.
    assert (s = store_bot) by eauto using crel_init. subst.
    assumption.
    destruct IH as (v & s''& R & V).
    eexists. eexists. split. eapply red_unbox_box;try eassumption;eauto. assumption.
  - (* unbox *)
    unfold trel in *. intros Hs' s' HsL TL CHs' Cs'.
    apply crel_mono with (Hs':=Hs') (s':=s') in C;auto.
    pose C as C'. apply crel_skip_now in C'.
    destruct C' as (Hs'' & Su & CHS & C').
    assert (exists (v : term) (s'' : store),
               {sub_app (sub_skip (skip_now_count G) g) t, store_bot}⇓ {v, s''} /\
               vrel (Box T) Hs'' s'' v) as IH by
        (eapply IHT; eauto using crel_skip_now, sub_skip_closed,heaps_single_closed).
    
    destruct IH as (v & s''& R & V).
    assert (store_le store_bot (s'')) as SL
        by eauto using red_extensive.
    inversion SL. subst.
    erewrite sub_skip_now_app in R by eauto.
    assert (exists h h', s' = store_lock h h') as S' by eauto using crel_now'.
    destruct S' as (h&h'&S'). rewrite S' in *.
    apply vrel_box_cases with (Hs' := Hs') (h := h) (h':=h') in V;eauto.

    destruct V.
    + autodest. eexists; eexists; split.
      simpl. eapply red_unbox_box;eauto. eauto.
    + autodest. eexists; eexists; split.
      simpl. eapply red_unbox_fix;eauto using heap_fresh_alloc. eauto.
  - (* promote (now context) *)    
    unfold trel in *. intros Hs' s' HsL TL CHs' Cs'.
    apply crel_mono with (Hs':=Hs') (s':=s') in C;auto.
    pose C as C'. apply crel_skip_now in C'.
    destruct C' as (Hs'' & Su & CHS & C').
    assert (exists (v : term) (s'' : store),
               {sub_app (sub_skip (skip_now_count G) g) t, store_bot}⇓ {v, s''} /\
               vrel T Hs'' s'' v) as IH by
        (eapply IHT; eauto using crel_skip_now, sub_skip_closed,heaps_single_closed).
    
    destruct IH as (v & s''& R & V).
    assert (store_le store_bot (s'')) as SL
        by eauto using red_extensive.
    inversion SL. subst. erewrite sub_skip_now_app in R by eauto.
    eexists. eexists. split. simpl.  apply red_promote.
    eapply R. eapply vrel_stable in V. apply V. auto. auto.
  - (* promote (later context) *)
    unfold trel in *. intros Hs' s' HsL TL CHs' Cs'.
    assert (exists hn hl : heap, s = store_lock (Some hn) hl) as ST by
          eauto using crel_later.
    destruct ST as (hn & hl & ST). subst.
    pose (tick_le_tick' _ _ _ TL) as ST.
    destruct ST as (hn' & hl' & [ST [HLn HLl]]). subst.
    dependent destruction Cs.
    dependent destruction Cs'.
    apply crel_mono with (Hs':=Hs') (s':=store_lock (Some hn) hl) in C;auto.
    pose C as C'. apply crel_skip_later in C'.
    apply crel_skip_now in C'.
    destruct C' as (Hs'' & Su & CHS & C').
    assert (exists (v : term) (s'' : store),
               {sub_app (sub_skip (skip_now_count (skip_later G))
                                  (sub_skip (skip_later_count G) g)) t, store_bot}⇓ {v, s''} /\
               vrel T Hs'' s'' v) as IH by
        (eapply IHT; eauto using crel_skip_now, sub_skip_closed,heaps_single_closed).
    
    destruct IH as (v & s''& R & V).
    assert (store_le store_bot (s'')) as SL
        by eauto using red_extensive.
    inversion SL. subst. simpl. erewrite sub_skip_both_app in R;eauto.
    eexists. eexists. split. simpl.  apply red_promote.
    eapply R. eapply vrel_stable in V. apply V. auto. 
    eauto using suffix_cons.
  - (* fixp *)
    assert (closed_term (sub_app g (fixp t))).
    eapply crel_sub_closed;eauto.
    
    apply vrel_trel. simpl. autorewrite with vrel.
    split. auto. intros Hs0 Su.
    apply suffix_wsuffix in Su.
    remember (length Hs0).
    generalize dependent Hs0.
    induction (lt_wf n) as [n _ IHn];intros Hs0 Su N;subst.

    unfold trel. intros Hs' s' HsL TL CHs' Cs'.
    assert (exists hn hl, s' = store_lock hn hl) as SS by
          eauto using tick_le_lock.
    destruct SS as (hn & hl & SS). subst.
    assert (s = store_bot) by eauto using crel_init. subst.
    pose (alloc_fresh hl) as l.
    
    pose (heapseq_le_suffix_trans _ _ _ Su HsL) as Su'.
    
    assert (vrel (Delay T) Hs'
               (store_lock hn (heap_cons hl l (unbox (fixp (sub_app (None :: g) t))))) (ref l)) as D.
    destruct Hs'.
    + rewrite vrel_delay_nil. eauto.
    + rewrite vrel_delay.

      eexists. eexists. split. reflexivity. split. apply store_mapsto_cons.
      intros. apply trel_mono with (Hs:= Hs') (s:=store_lock None heap_empty);auto.
      eauto using tick_le_none, heap_le_empty.
      eapply IHn with (y := length Hs').
      assert (length Hs0 = length (h :: Hs')) by eauto using heapseq_le_length.
      simpl in *. omega. eauto using wsuffix_trans, heapseq_le_cons_wsuffix.
      reflexivity.

      
    + assert (exists (v : term) (s'' : store),
                 {sub_app (Some (ref l) :: g) t,
                  store_lock hn (heap_cons hl l (unbox (fixp (sub_app (None :: g) t))))}⇓ {v, s''} /\
                 vrel T Hs' s'' v) as IH.
      eapply IHT ; try first [eapply crel_var; first[eapply D|eauto]|eassumption].
      inversion Su'. subst. eapply crel_mono with (Hs:=Hs2);try eassumption;eauto.
      dependent destruction Cs';eauto using closed_heap_alloc.
      eauto. dependent destruction Cs';eauto using closed_heap_alloc. auto.
      simpl. auto.
      dependent destruction Cs';eauto using closed_heap_alloc. 
      autodest.
      eexists. eexists. split. eapply red_unbox_fix; try eassumption. eauto.
      eauto using heap_fresh_alloc.  rewrite sub_term_merge. eauto. eauto. eauto.
  - (* into *)
    unfold trel in *. intros Hs' s' HsL TL CHs' Cs'.
    apply crel_mono with (Hs':=Hs') (s':=s') in C;auto.
    assert (exists (v : term) (s'' : store),
               {sub_app g t, s'}⇓ {v, s''} /\ vrel (tsubst 0 T (Delay (Mu T))) Hs' s'' v) as IH
        by (eapply IHT;try eassumption;eauto).
    destruct IH as (v & s''& R & V).
    eexists. eexists. split. simpl. apply red_into. apply R.
    rewrite vrel_mu. eauto.
  - (* out *)
    unfold trel in *. intros Hs' s' HsL TL CHs' Cs'.
    apply crel_mono with (Hs':=Hs') (s':=s') in C;auto.
    assert (exists (v : term) (s'' : store), {sub_app g t, s'}⇓ {v, s''}
                                             /\ vrel (Mu A) Hs' s'' v) as IH
        by (eapply IHT;try eassumption;eauto).
    destruct IH as (v & s''& R & V).
    rewrite vrel_mu in V.
    destruct V as (v' & E & V). subst.
    eexists. eexists. split. simpl. apply red_out. apply R. apply V.
Qed.
    
