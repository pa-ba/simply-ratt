(* This module defines the big-step operational semantics. *)

From SimplyRatt Require Export TypingClosed Worlds.

From SimplyRatt Require Import Tactics.

From Coq Require Import Program.Equality  Omega.


Reserved Notation " '{' t ',' h '}' '⇓' '{' t' ','  h' '}' " (at level 40).
Inductive red : term -> store -> term -> store -> Prop :=
(* Value reductions *)
| red_value v h : isvalue v -> 
    {v,h} ⇓ {v,h}
(* Expression reductions *)
| red_pair     : forall (t1 t2 v1 v2 : term) (h h' h'' : store),
    {t1,h} ⇓ {v1,h'} ->
    {t2,h'} ⇓ {v2,h''} ->
    {pair t1 t2,h} ⇓ {pair v1 v2, h''}
| red_pr1       : forall (t v1 v2 : term) (h h' : store),
    {t,h} ⇓ {pair v1 v2,h'} -> 
    {pr1 t, h} ⇓ {v1,h'}
| red_pr2       : forall (t v1 v2 : term) (h h' : store),
    {t,h} ⇓ {pair v1 v2,h'} -> 
    {pr2 t, h} ⇓ {v2,h'}
| red_in1      : forall (t v : term) (h h' : store),
    {t,h} ⇓ {v,h'} ->
    {in1 t,h} ⇓ {in1 v,h'}
| red_in2      : forall (t v : term) (h h' : store),
    {t,h} ⇓ {v,h'} ->
    {in2 t,h} ⇓ {in2 v,h'}
| red_case1     : forall (t t1 t2 v v' : term) (h h' h'' : store),
    {t,h} ⇓ {in1 v, h'} ->
    {sub_term t1 v , h'} ⇓ {v',h''} ->
    {case t t1 t2, h} ⇓ {v',h''}
| red_case2     : forall (t t1 t2 v v' : term) (h h' h'' : store),
    {t,h} ⇓ {in2 v, h'} ->
    {sub_term t2 v,h'} ⇓ {v',h''} ->
    {case t t1 t2, h} ⇓ {v',h''}
| red_app t t' t'' v v' h h' h'' h''' :
    {t,h} ⇓ {abs t'',h'} ->
    {t',h'} ⇓ {v,h''} ->
    {sub_term t'' v,h''} ⇓ {v',h'''} ->
    {app t t',h} ⇓ {v',h'''}
| red_delay t h h' :
    {delay t, store_lock h' h } ⇓ {ref (alloc_fresh h), store_lock h' (heap_cons h (alloc_fresh h) t)}
| red_adv t t' v l hn he he' h:
    {t,store_lock None he} ⇓ {ref l, store_lock None he'}  ->
    heap_mapsto l t' he' -> 
    {t',store_lock (Some he') hn} ⇓ {v,h}  ->
    {adv t,store_lock (Some he) hn} ⇓ {v,h}
| red_progr t v hn he he' :
    {t,store_lock None he} ⇓ {v, store_lock None he'}  ->
    {progr t,store_lock (Some he) hn} ⇓ {v,store_lock (Some he') hn}
| red_promote  t v  s :
    {t,store_bot} ⇓ {v,store_bot} ->
    {promote t,s} ⇓ {v,s}
| red_unbox_box t t' v s s' :
    {t,store_bot} ⇓ {box t',store_bot} ->
    {t', s} ⇓ {v,s'} ->
    {unbox t,s} ⇓ {v,s'}
| red_unbox_fix t t' v h h' s :
    {t,store_bot} ⇓ {fixp t',store_bot} ->
    {sub_term t' (ref (alloc_fresh h)), store_lock h' (heap_cons h (alloc_fresh h) (unbox (fixp t')))} ⇓ {v,s} ->
    {unbox t,store_lock h' h} ⇓ {v,s}
| red_into       : forall h h' t v,
    {t,h} ⇓ {v,h'} ->
    {into t,h} ⇓ {into v,h'}
| red_out        : forall h h' t v,
    {t,h} ⇓ {into v,h'} ->
    {out t,h} ⇓ {v,h'}
where  " '{' t ',' h '}' '⇓' '{' t' ','  h' '}' " := (red t h t' h').


Hint Constructors red.

  
Lemma red_extensive t t' h h' : red t h t' h' -> store_le h h'.
Proof.
  intros R. induction R;eauto using store_le_trans.
  - destruct h'; constructor; eauto using heap_cons_mono,heap_fresh_alloc.
  - inversion IHR1. subst. inversion IHR2. subst.
    eauto using heap_le_trans.
  - inversion IHR. subst. eauto using heap_le_trans.
  - inversion IHR2; subst; constructor;
    eauto using heap_cons_mono, heap_le_trans,heap_fresh_alloc.
Qed. 




Lemma closed_heap_alloc h t l : closed_heap h -> closed_term t -> closed_heap (heap_cons h l t).
Proof.
  intros. intros l' t' M.
  pose (Nat.eq_decidable l l') as EQ. 
  destruct EQ as [EQ | EQ].
  - subst. rewrite heap_cons_mapsto_eq in M. subst. eauto. 
  - rewrite heap_cons_mapsto_neq in M by auto. eauto.
Qed.

Lemma red_closed t t' s s' : closed_term t -> closed_store s -> red t s t' s' -> closed_term t' /\ closed_store s'.
Proof.
  intros C CS R. induction R;try solve[eauto; constructor;inversion C; subst; eauto].
  - (* pair *)
    inversion C; subst. apply IHR1 in H2; auto.
    destruct H2 as [IH1F IH1C]. apply IHR2 in H3;auto.
    destruct H3 as [IH2F IH2C]. eauto.
  - (* pr1 *)
    inversion C; subst. apply IHR in H1.
    destruct H1 as [IHF IHC]. 
    inversion IHF;auto. auto.
  - (* pr2 *)
    inversion C; subst. apply IHR in H1.
    destruct H1 as [IHF IHC]. 
    inversion IHF;auto. auto.
  - (* in1 *)
    inversion C; subst. apply IHR in H1;auto.
    destruct H1 as [IHF IHC]. eauto.
  - (* in2 *)
    inversion C; subst. apply IHR in H1;auto.
    destruct H1 as [IHF IHC]. eauto.
  - (* case in1 *)
    inversion C; subst. apply IHR1 in H3;auto.
    destruct H3 as [IH1F IH1C].
    dependent destruction IH1F. apply IHR2 in IH1C;auto.
    apply sub_term_closed;auto.
  - (* case in2 *)
    inversion C; subst. apply IHR1 in H3;auto.
    destruct H3 as [IH1F IH1C].
    dependent destruction IH1F. apply IHR2 in IH1C;auto.
    apply sub_term_closed;auto.
  - (* app *)
    dependent destruction C.
    apply IHR1 in C1;auto.
    destruct C1 as [IH1F IH1C].
    apply IHR2 in C2;auto.
    destruct C2 as [IH2F IH2C].
    apply IHR3 in IH2C;auto.
    dependent destruction IH1F.
    apply sub_term_closed;auto.
  - (* delay *)
    split. auto. dependent destruction C.
    dependent destruction CS;constructor;eauto using closed_heap_alloc.
  - (* adv *)
    inversion C; subst. inversion CS;subst. apply IHR1 in H2;auto.
    destruct H2 as [IH1F IH1C]. inversion IH1C;subst. apply H1 in H.
    apply IHR2 in H;auto.
  - (* progress *)
    dependent destruction C. dependent destruction CS.
    apply IHR in C;auto.
    destruct C as [IHF IHC]. dependent destruction IHC. auto.
  - (* promote *)
    dependent destruction C. 
    apply IHR in C;auto. destruct C as [IHF IHC]. auto.
  - (* unbox box *)
    dependent destruction C. apply IHR1 in C;auto.
    destruct C as [IH1F IH1C]. dependent destruction IH1F.
    eauto.
  - (* unbox fixp *)
    dependent destruction C. apply IHR1 in C;auto.
    destruct C as [IH1F IH1C]. dependent destruction IH1F.
    apply IHR2.
    + apply sub_term_closed;auto. 
    + dependent destruction CS; constructor;eauto using closed_heap_alloc.
  - (* into *)
    dependent destruction C. apply IHR in C;auto.
    destruct C as [IHF IHC]. eauto.
  - (* out *)
    dependent destruction C. apply IHR in C;auto.
    destruct C as [IHF IHC]. dependent destruction IHF. eauto.
Qed.

Lemma red_isvalue_id v v' s s' : isvalue v -> red v s v' s' -> v = v' /\ s = s'.
Proof.
  intros V R. generalize dependent v'. generalize dependent s. generalize dependent s'.
  induction V;intros;inversion R;subst; eauto.
  - apply IHV in H0. autodest.
  - apply IHV1 in H1. apply IHV2 in H5. autodest.
  - apply IHV in H0. autodest.
  - apply IHV in H0. autodest.
Qed.

Ltac inv_value := match goal with
                  | [H : isvalue _ |- _] => inversion H;subst
                  | _ => subst
                  end.


Lemma red_determ t s t1 t2 s1 s2 : red t s t1 s1 -> red t s t2 s2 -> t1 = t2 /\ s1 = s2.
Proof.
  intros R1. generalize dependent t2. generalize dependent s2. induction R1;intros s_2 t_2 R2.
  - eauto using red_isvalue_id.
  - inversion R2;subst. inversion H.
    + subst. eapply red_value in H2. eapply red_value in H3.
      apply IHR1_1 in H2. apply IHR1_2 in H3. autodest.
    + apply IHR1_1 in H1. autodest. apply IHR1_2 in H5. autodest.
  - dependent destruction R2. inv_value. apply IHR1 in R2. autodest.
    inversion H. subst. auto.
  - dependent destruction R2. inv_value. apply IHR1 in R2. autodest.
    inversion H. subst. auto.
  - dependent destruction R2; inv_value.  eapply red_value in H1. eapply IHR1 in H1. autodest.
    apply IHR1 in R2. autodest.
  - dependent destruction R2. inv_value.  eapply red_value in H1. eapply IHR1 in H1. autodest.
    apply IHR1 in R2. autodest.
  - dependent destruction R2; inv_value.
    + apply IHR1_1 in R2_1. autodest. inversion H. subst.
      apply IHR1_2 in R2_2. autodest. 
    + apply IHR1_1 in R2_1. autodest. inversion H. 
  - dependent destruction R2; inv_value.
    + apply IHR1_1 in R2_1. autodest. inversion H.
    + apply IHR1_1 in R2_1. autodest. inversion H. subst.
      apply IHR1_2 in R2_2. autodest. 
  - dependent destruction R2; inv_value.
    apply IHR1_1 in R2_1. autodest. inversion H. subst.
    apply IHR1_2 in R2_2. autodest. 
  - dependent destruction R2; inv_value. auto.
  - dependent destruction R2; inv_value.
    apply IHR1_1 in R2_1. autodest. inversion H1. inversion H2. subst.
    eapply heap_mapsto_determ in H;eauto. subst.
    apply IHR1_2 in R2_2. autodest.
  - dependent destruction R2; inv_value. 
    apply IHR1 in R2. autodest. inversion H0. subst. auto.
  - dependent destruction R2; inv_value. 
    apply IHR1 in R2. autodest.
  - dependent destruction R2; inv_value.
    + apply IHR1_1 in R2_1. autodest. inversion H. subst. auto.
    + apply IHR1_1 in R2_1. autodest. inversion H. 
  - dependent destruction R2; inv_value.
    + apply IHR1_1 in R2_1. autodest. inversion H. 
    + apply IHR1_1 in R2_1. autodest. inversion H. subst. auto.
  - dependent destruction R2; inv_value.
    + eapply red_value in H1. apply IHR1 in H1. autodest.
    + apply IHR1 in R2. autodest.
  - dependent destruction R2; inv_value.
    apply IHR1 in R2. autodest. inversion H. subst. auto.
Qed.