(* Here we prove properties about the logical relation such as
   monotonicity under tick_le and heapseq_le *)

From SimplyRatt Require Export LogicalRelation. 

From SimplyRatt Require Import Tactics.

From Coq Require Import Program.Equality Omega.

Lemma vrel_gc A : forall Hs s t, vrel A Hs s t -> vrel A Hs (gc s) t.
Proof.
  remember (tsize A) as N. generalize dependent A.
  induction (lt_wf N) as [N _ IH]. intros.
  destruct A; try solve[autorewrite with vrel in *;eauto].
  - rewrite vrel_times in *. autodest.
    exists x, x0. split. reflexivity. split.
    + eapply (IH (tsize A1));[simpl; omega|eauto|eauto].
    + eapply (IH (tsize A2));[simpl; omega|eauto|eauto].
  - rewrite vrel_plus in *. autodest.
    + left. exists x. split. reflexivity. eapply (IH (tsize A1));[simpl; omega|eauto|eauto].
    + right. exists x. split. reflexivity. eapply (IH (tsize A2));[simpl; omega|eauto|eauto].
  - rewrite vrel_arrow in *. autodest. exists x. split. reflexivity. intros.
    rewrite gc_idem in *. apply H0;eauto.
  - destruct Hs.
    + rewrite vrel_delay_nil in *. assumption.
    + rewrite vrel_delay in *. autodest.
      exists x, x0. split. reflexivity. split. apply store_mapsto_gc; assumption.
      intros. rewrite store_tick_gc. auto.
  - rewrite vrel_mu in *. autodest. exists x. split. reflexivity.
    apply (IH (tsize (tsubst 0 A (Delay (Mu A))))). rewrite tsize_subst. auto. auto. auto.
Qed.

Lemma trel_mono A Hs Hs' s s' t : heapseq_le Hs Hs' -> tick_le s s' ->  trel A Hs s t -> trel A Hs' s' t.
Proof.
  unfold trel in *. intros.
  assert (heapseq_le Hs Hs'0) as A1 by eauto using heapseq_le_trans.
  assert (tick_le s s'0) as A2 by eauto using tick_le_trans.
  remember (H1  Hs'0 s'0 A1 A2) as A3. clear HeqA3 H1. autodest.
Qed.
  

Lemma vrel_mono A : forall Hs Hs' s s' t, heapseq_le Hs Hs' -> tick_le s s' ->  vrel A Hs s t -> vrel A Hs' s' t.
Proof.
  remember (tsize A) as N. generalize dependent A.
  induction (lt_wf N) as [N _ IH]. intros. destruct A; try solve[autorewrite with vrel in *;eauto].
  - rewrite vrel_times in *. autodest.
    exists x, x0. split. auto. split.
    + eapply (IH (tsize A1)); eauto. simpl. omega.
    + eapply (IH (tsize A2)); eauto. simpl. omega.
  - rewrite vrel_plus in *. autodest.
    + left. exists x. split. auto. eapply (IH (tsize A1)); eauto. simpl. omega.
    + right. exists x. split. auto. eapply (IH (tsize A2)); eauto. simpl. omega.
  - rewrite vrel_arrow in *. autodest.
    exists x. split. auto. intros.
    apply H2; eauto using heapseq_le_trans, store_le_trans, tick_le_gc.
  - destruct Hs.
    + inversion H. subst. rewrite vrel_delay_nil in *. auto.
    + inversion H. subst. rewrite vrel_delay in *. autodest.
      exists x, x0. split. auto. split. eauto using tick_le_mapsto.
      intros. apply H4 in H1. autodest.
      eapply trel_mono. eassumption. eapply tick_le_store_tick. eassumption.
      eassumption. auto.
  - rewrite vrel_box in *. autodest.
    split. assumption. intros. remember (heapseq_le_suffix _ _ _ H H3) as Su. clear HeqSu.
    autodest. eapply trel_mono. eassumption. econstructor. econstructor. apply heap_le_refl.
    apply H2. assumption.
  - rewrite vrel_mu in *. autodest. exists x. split. auto.
    eapply (IH (tsize (tsubst 0 A (Delay (Mu A))))); try rewrite tsize_subst; eauto. 
Qed.


Lemma vrel_gc_rev A : forall Hs s t, vrel A Hs (gc s) t -> vrel A Hs s t.
Proof.
  intros. eauto using vrel_mono, tick_le_gc'.
Qed. 


Lemma vrel_stable A : forall Hs Hs' s s' t, stable A -> suffix Hs' Hs -> vrel A Hs s t -> vrel A Hs' s' t.
Proof.
  remember (tsize A) as N. generalize dependent A.
  induction (lt_wf N) as [N _ IH]. intros A HN Hs Hs' s s' t ST SU VR.
  destruct A; inversion ST; try solve[autorewrite with vrel in *;eauto].
  - rewrite vrel_times in *. autodest. exists x, x0.
    split. auto. split.
    + eapply (IH (tsize A1)); simpl; eauto; try omega.
    + eapply (IH (tsize A2)); simpl; eauto; try omega.
  - rewrite vrel_plus in *. autodest.
    + left. exists x. split. auto. eapply (IH (tsize A1)); simpl; eauto; try omega.
    + right. exists x. split. auto. eapply (IH (tsize A2)); simpl; eauto; try omega.
  - rewrite vrel_box in *. autodest. split. auto. intros. apply H1. eauto using suffix_trans.
Qed.

Lemma vrel_trel A Hs s t : vrel A Hs s t -> trel A Hs s t.
Proof.
  intros. assert (isvalue t) by eauto using vrel_val. unfold trel.
  intros. exists t, s'. split. apply red_value. auto. eauto using vrel_mono.
Qed.


(* context relation *)


Lemma crel_init (G : ctx init) Hs s g : crel G Hs s g -> s = store_bot.
Proof.
  intros C. dependent induction C;eauto.
Qed.

Lemma crel_now (G : ctx now) Hs s g : crel G Hs s g -> s <> store_bot.
Proof.
  intros C. dependent induction C;eauto.
Qed.

Lemma crel_now' (G : ctx now) Hs s g : crel G Hs s g -> 
                                   exists hn hl, s = store_lock hn hl.
Proof.
  intros C. apply crel_now in C. destruct s; eauto. contradiction.
Qed.

Lemma crel_later (G : ctx later) Hs s g : crel G Hs s g ->
                                   exists hn hl, s = store_lock (Some hn) hl.
Proof.
  intros C. dependent induction C;eauto.
Qed.

Lemma crel_gc ty (G : ctx ty) Hs s g : ty <> later -> crel G Hs s g -> crel G Hs (gc s) g.
Proof.
  intros T C; induction C.
  - simpl. auto.
  - simpl. eauto using vrel_gc.
  - auto.
  - eapply crel_lock; try eassumption. rewrite <- store_bot_gc. assumption. 
  - contradiction.
Qed.

Lemma heaps_single_closed h : closed_heap h -> closed_heaps (heaps_single h).
Proof.
  intro C. intros h' H. inversion H. auto.
Qed.

Hint Resolve heaps_single_closed.

Lemma crel_mono ty (G : ctx ty) Hs Hs' s s' g :
  heapseq_le Hs Hs' -> closed_heapseq Hs' ->
  tick_le s s' -> closed_store s' ->  crel G Hs s g -> crel G Hs' s' g.
Proof.
  intros HS CL T CS C. generalize dependent Hs'. generalize dependent s'.
  induction C;intros.
  - inversion T. subst. inversion H. subst. eauto.
  - eauto using vrel_mono.
  - eauto.
  - pose (heapseq_le_suffix'' _ _ _ HS H H0 CL) as HL. autodest. eapply crel_lock;
    try eassumption. pose (tick_le_bot' _ _ T) as B. apply B. assumption.
    eauto.
  - inversion T. subst. inversion H. subst.
    dependent destruction CS.
    apply crel_tick.
    apply IHC;eauto using heaps_single_le.
Qed.


Lemma crel_skip_later g hn hl G Hs :
  crel G Hs (store_lock (Some hn) hl) g ->
  crel (skip_later G)
       (heaps_single hl :: Hs) (store_lock None hn) (sub_skip (skip_later_count G) g).
Proof.
  intros C. dependent induction C;simpl;eauto.
Qed.

Lemma crel_skip_now g G Hs s :
  crel G Hs s g -> exists Hs', suffix Hs Hs' /\ closed_heapseq Hs' /\
  crel (skip_now G) Hs' store_bot (sub_skip (skip_now_count G) g).
Proof.
  intros C. dependent induction C.
  - simpl. pose (IHC G0 eq_refl JMeq_refl) as IH. autodest.
  - simpl. pose (IHC G0 eq_refl JMeq_refl) as IH. autodest.
  - eauto.
Qed.

Lemma crel_ground ty (G : ctx ty) Hs s g : crel G Hs s g -> ground_sub 0 g G.
Proof.
  intros CR. induction CR; eauto.
Qed.

Lemma crel_sub_closed ty g (G : ctx ty) Hs s A t :
      G ⊢ t ∶ A -> closed_sub g -> crel G Hs s g -> closed_term (sub_app g t).
Proof.
  intros. eapply ground_sub_closed;eauto using crel_ground.
Qed.


Lemma ctx_lookup_vrel ty (G : ctx ty) i T Hs s g :
  ctx_lookup G i T -> crel G Hs s g -> exists t, sub_lookup g i = Some t /\ vrel T Hs s t.
Proof.
  intros L C. generalize dependent g. induction L;intros.
  - dependent destruction C. eexists. split. cbv. reflexivity. assumption.
  - dependent destruction C. apply IHL in C. autodest.
  - dependent destruction C. apply IHL in C. autodest.
Qed.



Lemma sub_skip_later_app Hs s g G t A : skip_later G ⊢ t ∶ A -> crel G Hs s g ->
                                      sub_app (sub_skip (skip_later_count G) g) t = sub_app g t.
Proof.
  intros. apply sub_skips_id. eapply typing_svars;try eassumption. apply skip_later_skipn.
Qed.

Lemma sub_skip_now_app Hs s g G t A : skip_now G ⊢ t ∶ A -> crel G Hs s g ->
                                      sub_app (sub_skip (skip_now_count G) g) t = sub_app g t.
Proof.
  intros. apply sub_skips_id. eapply typing_svars;try eassumption. apply skip_now_skipn.
Qed.

Lemma sub_skip_both_app Hs s g G t A :
  skip_now (skip_later G) ⊢ t ∶ A -> crel G Hs s g ->
  sub_app (sub_skip (skip_now_count (skip_later G)) (sub_skip (skip_later_count G) g)) t
           = sub_app g t.
Proof.
  intros. rewrite sub_skips_id. apply sub_skips_id. eapply typing_svars;try eassumption.
  apply ctx_skips_now.  apply skip_later_skipn.
  eapply typing_svars;try eassumption. apply skip_now_skipn.
Qed.    

Lemma crel_now_lock (G : ctx now) Hs s g : crel G Hs (gc s) g ->
                                           exists h, gc s = store_lock None h.
Proof.
  intros C.
  apply crel_now in C. destruct s.
  - simpl in C. contradiction.
  - simpl in *. eauto.
Qed.


Inductive vtype : type -> Prop :=
| vtype_unit : vtype Unit
| vtype_nat : vtype Nat
| vtype_times A B :
    vtype A ->
    vtype B ->
    vtype (Times A B)
| vtype_plus A B :
    vtype A ->
    vtype B ->
    vtype (Plus A B).

Lemma vtype_typing A Hs s v : vtype A -> vrel A Hs s v -> ctx_empty ⊢ v ∶ A.
Proof.
  intros VT VR. generalize dependent v.
  induction VT; intros; autorewrite with vrel in VR;autodest.
Qed.

Ltac impossible := match goal with
                   | [H : _ |- _] => try solve[inversion H]; clear H;impossible
                   | _ => idtac
                   end.

Lemma typing_vtype A Hs s v : vtype A -> isvalue v -> ctx_empty ⊢ v ∶ A -> vrel A Hs s v.
Proof.
  intros VT V Ty. generalize dependent v.
  induction VT;intros;
    dependent destruction Ty;try solve[impossible];inversion V;subst; autorewrite with vrel in *;eauto.
    do 2 eexists. eauto.
Qed.


Lemma vtype_vrel A Hs s Hs' s' v : vtype A -> vrel A Hs s v -> vrel A Hs' s' v.
Proof.
  intros VT VR. generalize dependent v.
  induction VT; intros; autorewrite with vrel in *;autodest;
  eauto 10.
Qed.


Lemma vtype_tsubst i A B : vtype A -> tsubst i A B = A.
Proof.
  intros VT. induction VT;simpl;f_equal;eauto.
Qed.



Lemma vrel_delay_closed A Hs s v : vrel (Delay A) Hs s v -> closed_term v.
Proof.
  intros V. destruct Hs; autorewrite with vrel in V; autodest.
Qed. 


Lemma vtype_vrel_closed A Hs s v : vtype A -> vrel A Hs s v -> closed_term v.
  intros VT. generalize dependent v. induction VT;intros v VR;autorewrite with vrel in VR;
                                       autodest.
Qed.
  

  

Lemma vtype_inhab A : vtype A -> exists v, vrel A nil store_bot v.
Proof.
  intros VT. induction VT.
  - exists unit. autorewrite with vrel in *. auto.
  - exists (natlit 0). autorewrite with vrel in *. eauto.
  - autodest. eexists. autorewrite with vrel in *. eauto.
  - autodest. eexists. autorewrite with vrel in *. eauto.
Qed.



Lemma trel_app T1 T2 Hs s t1 t2 :
  closed_term t1 -> closed_term t2 ->
  trel (Arrow T1 T2) Hs s t1 -> trel T1 Hs s t2 ->
  trel T2 Hs s (app t1 t2).
Proof.
  unfold trel in *. intros Ct1 Ct2 IHT1 IHT2 Hs' s' HS TL HCH HCs.
  pose (IHT1 _ _ HS TL HCH HCs) as IH1.
  destruct IH1 as (v & s''& [IH1s IH1v]).
  rewrite vrel_arrow in IH1v.
  destruct IH1v as (u & [V IH1]). subst.
  assert (tick_le s s'') as TL' by eauto using tick_le_trans, red_extensive.
  assert (closed_term (abs u) /\ closed_store s'') as HCC by
        (apply red_closed with (t := t1) (s := s');eauto).
  destruct HCC as [HC'' HCs'].
  pose (IHT2 _ _ HS TL' HCH HCs') as IH2.
  destruct IH2 as (v' & s'''& [IH2s IH2v]).
  apply vrel_gc in IH2v.
  assert (store_le (gc s'') (gc s''')) as SL by
          eauto using tick_le_gc,red_extensive.
  assert (closed_term v' /\ closed_store s''') as CT by
        (apply red_closed with (t := t2) (s := s'');eauto using crel_sub_closed).
    destruct CT as [CT CTS].
    assert (closed_store (gc s''')) as CGS by (eauto using closed_store_gc).
    pose (IH1 _ (gc s''') (heapseq_le_refl _) SL HCH CGS v' IH2v CT _ _ (heapseq_le_refl _)
              (tick_le_gc' s''') HCH CTS) as IH1v.
    destruct IH1v as (w & s1 & [R V]).
    exists w, s1. simpl. eauto.
Qed. 

Lemma trel_adv l hl hn Hs A t:
  heap_mapsto l t hn ->
  trel A Hs (store_lock (Some hn) hl) t ->
  trel A Hs (store_lock (Some hn) hl) (adv (ref l)).
Proof.
  intros M Tt. unfold trel in *. intros.
  assert (exists (v : term) (s'' : store), {t, s'}⇓ {v, s''} /\ vrel A Hs' s'' v)
    as Tt' by eauto.
  autodest. apply tick_le_tick' in H0. autodest.
  do 2 eexists. split.
  eapply red_adv. constructor. auto. eauto.  eauto. eauto.
Qed.
