From SimplyRatt Require Export Heaps ClosedTerms.

From SimplyRatt Require Import Tactics.

From Coq Require Import Omega Program.Equality.



(* Definition of heaps *)
Inductive store : Type :=
| store_bot  : store
| store_lock : option heap -> heap -> store.

Bind Scope heap_scope with heap. 
Open Scope heap_scope.

Definition gc (s : store) :=
  match s with
  | store_bot => store_bot
  | store_lock _ h => store_lock None h
  end.

Definition store_tick (s : store) (h : heap) : store :=
  match s with
  | store_bot => store_bot
  | store_lock _ h' => store_lock (Some h') h
  end.

Inductive store_mapsto : loc -> term -> store -> Prop :=
| store_mapsto_heap l t h h' : heap_mapsto l t h -> store_mapsto l t (store_lock h' h).

Hint Constructors store_mapsto.

(* freshness for heaps *)
    

(* orders on heaps and stores *)

Definition heap_le (h1 h2 : heap) : Prop := forall x e, heap_mapsto x e h1 -> heap_mapsto x e h2
.
Inductive store_le : store -> store -> Prop :=
| store_le_bot : store_le store_bot store_bot
| store_le_lock h h' : heap_le h h' -> store_le (store_lock None h) (store_lock None h')
| store_le_tick h1 h1' h2 h2' : heap_le h1 h1' -> heap_le h2 h2' ->
                                store_le (store_lock (Some h1) h2) (store_lock (Some h1') h2').

Inductive tick_le : store -> store -> Prop :=
| tick_le_store s s' : store_le s s' -> tick_le s s'
| tick_le_tick h1 h2 h2' : heap_le h2 h2' ->
                           tick_le (store_lock None h2) (store_lock (Some h1) h2').

Hint Constructors store_le tick_le.

Definition heaps := heap -> Prop.

Definition heaps_le (H H' : heaps) : Prop :=
  forall h', H' h' -> exists h, H h /\ heap_le h h'.

Definition heapseq := list heaps.

Notation heapseq_le := (Forall2 heaps_le).

Inductive suffix (Hs : heapseq) :  heapseq -> Prop :=
| suffix_drop H Hs' : suffix Hs Hs' -> suffix Hs (H :: Hs')
| suffix_refl : suffix Hs Hs.

Inductive wsuffix : heapseq -> heapseq -> Prop :=
  wsuffix_split Hs1 Hs2 Hs3 : heapseq_le Hs2 Hs1 -> suffix Hs2 Hs3 -> wsuffix Hs1 Hs3.

Hint Constructors suffix wsuffix.

(* reflexivity and transitivity of the above orders *)

Lemma suffix_trans Hs1 Hs2 Hs3 : suffix Hs1 Hs2 -> suffix Hs2 Hs3 -> suffix Hs1 Hs3.
Proof.
  intros S1 S2. induction S2;eauto.
Qed.

Lemma heap_le_refl h : heap_le h h.
Proof.
  unfold heap_le. intros. auto.
Qed. 

Lemma heaps_le_refl H : heaps_le H H.
Proof.
  unfold heaps_le. intros. exists h'. eauto using heap_le_refl.
Qed.


Lemma heapseq_le_refl Hs : heapseq_le Hs Hs.
Proof.
  induction Hs; constructor; eauto using heaps_le_refl.
Qed. 



Lemma store_le_refl s : store_le s s.
Proof.
  destruct s;try destruct o;eauto using heap_le_refl.
Qed.

Lemma tick_le_refl s : tick_le s s.
Proof.
  destruct s;eauto using store_le_refl.
Qed. 

Lemma heap_le_trans s1 s2 s3 : heap_le s1 s2 -> heap_le s2 s3 -> heap_le s1 s3.
Proof.
  unfold heap_le. intros. eauto.
Qed. 

Lemma store_le_trans s1 s2 s3 : store_le s1 s2 -> store_le s2 s3 -> store_le s1 s3.
Proof.
  intros T1 T2. destruct T1; inversion T2;eauto using heap_le_trans.
Qed.
  
Lemma tick_le_trans s1 s2 s3 : tick_le s1 s2 -> tick_le s2 s3 -> tick_le s1 s3.
Proof.
  intros T1 T2. destruct T1;inversion T2;subst;eauto using store_le_trans.
  -  inversion H. subst. apply tick_le_tick. eauto using heap_le_trans.
  - inversion H0. subst. apply tick_le_tick. eauto using heap_le_trans.
Qed .
                                

Lemma heaps_le_trans H1 H2 H3 : heaps_le H1 H2 -> heaps_le H2 H3 -> heaps_le H1 H3.
Proof.
  unfold heaps_le. intros.
  remember (H0 h' H4) as As. clear HeqAs H0.
  destruct As. destruct H0.
  remember (H x H0) as As2. clear HeqAs2 H.
  destruct As2. destruct H. eauto using heap_le_trans.
Qed.

Lemma heapseq_le_trans Hs1 Hs2 Hs3 : heapseq_le Hs1 Hs2 -> heapseq_le Hs2 Hs3 -> heapseq_le Hs1 Hs3.
Proof.
  intros S1 S2. generalize dependent Hs3.
  induction S1;intros;inversion S2;subst;eauto using heaps_le_trans.
Qed.


Lemma tick_le_lock hn hl s : tick_le (store_lock hn hl) s ->
                             exists hn' hl', s = store_lock hn' hl'.
Proof.
  intros L. dependent destruction L.
  - dependent destruction H; eauto.
  - eauto.
Qed.



Lemma suffix_cons1 H Hs Hs' :
  suffix (H :: Hs) Hs' -> exists H' Hs'', Hs' = H' :: Hs''.
Proof.
  intros Su. inversion Su; subst. eauto. eexists. eexists. reflexivity.
Qed.


Lemma heapseq_le_cons1 H Hs Hs' :
  heapseq_le (H :: Hs) Hs' -> exists H' Hs'', Hs' = H' :: Hs''.
Proof.
  intros L. inversion L. subst. eauto.
Qed.

Lemma heapseq_le_cons2 H Hs Hs' :
  heapseq_le  Hs' (H :: Hs) -> exists H' Hs'', Hs' = H' :: Hs''.
Proof.
  intros L. inversion L. subst. eauto.
Qed.

Lemma tick_le_none hl hl' hn :
  heap_le hl hl' -> tick_le (store_lock None hl) (store_lock hn hl').
Proof.
  intros. destruct hn;eauto.
Qed.

Lemma suffix_cons H Hs Hs' : suffix (H :: Hs) Hs' -> suffix Hs Hs'.
Proof.
  intros Su. induction Su; eauto.
Qed.


Lemma skipn_skipn A n n' (l : list A) : skipn n (skipn n' l) = skipn (n' + n) l.
Proof.
  generalize dependent l. induction n'; intros; simpl; eauto. destruct l.
  + destruct n;reflexivity.
  + eauto.
Qed.


Lemma heapseq_le_length Hs Hs' : heapseq_le Hs Hs' -> length Hs = length Hs'.
Proof.
  intros L. induction L;simpl;eauto.
Qed.

(* Other properties of the orderings *)

Lemma heap_le_dom h h' l : heap_le h h' -> heap_dom l h -> heap_dom l h'.
Proof.
  intros L D. destruct D as (t & D). apply L in D. eexists. eauto.
Qed.


Lemma heapseq_le_len Hs Hs' : heapseq_le Hs Hs' -> length Hs = length Hs'.
Proof.
  intros. induction H.
  - reflexivity.
  - simpl. rewrite IHForall2. reflexivity.
Qed. 


Lemma suffix_nil Hs : suffix Hs nil -> Hs = nil.
Proof.
  intros S. inversion S. reflexivity.
Qed. 

Lemma suffix_nil' Hs : suffix nil Hs.
Proof.
  induction Hs; eauto.
Qed. 


Lemma suffix_length Hs1 Hs2 : suffix Hs1 Hs2 -> length Hs1 <= length Hs2.
Proof.
  intros Su. induction Su. simpl. omega. omega.
Qed. 

Lemma suffix_length_skip Hs1 Hs2 : suffix Hs1 Hs2 -> skipn (length Hs2 - length Hs1) Hs2 = Hs1.
Proof.
  intros Su. induction Su. assert (length (H :: Hs') = S (length Hs')) as L1 by reflexivity.
  rewrite L1. rewrite <- minus_Sn_m by auto using suffix_length. auto.
  rewrite Nat.sub_diag. auto.
Qed. 


Lemma skip_suffix n Hs : suffix (skipn n Hs) Hs.
Proof.
  generalize dependent Hs. induction n;intros.
  + auto.
  + destruct Hs.
    * auto.
    * simpl. constructor. apply IHn.
Qed.

Lemma store_le_mapsto l t s s' : store_le s s' -> store_mapsto l t s -> store_mapsto l t s'.
Proof.
  intros SL SM. destruct SL;inversion SM; autodest.
Qed.

Lemma tick_le_mapsto l t s s' : tick_le s s' -> store_mapsto l t s -> store_mapsto l t s'.
Proof.
  intros SL SM; destruct SL.
  - eauto using store_le_mapsto.
  - inversion SM; autodest. 
Qed. 


Lemma heap_cons_mono l h x: heap_fresh l h -> heap_le h (heap_cons h l x).
Proof.
  unfold heap_le, heap_fresh. intros.
  pose (Nat.eq_decidable l x0) as EQ. destruct EQ. subst.
  assert (exists e,heap_mapsto x0 e h) by eauto. contradiction.
  apply heap_cons_mapsto_neq;eauto.
Qed.


Lemma mapsto_heap_cons l t h : heap_mapsto l t (heap_cons h l t).
Proof.
  rewrite heap_cons_mapsto_eq. auto.
Qed.


Lemma store_mapsto_cons l t h h' : store_mapsto l t (store_lock h' (heap_cons h l t)).
Proof.
  eauto using mapsto_heap_cons.
Qed.

Lemma tick_le_store_tick s s' h h' : tick_le s s' -> heap_le h h' -> tick_le (store_tick s h) (store_tick s' h').
Proof.
  intros. destruct s.
  - inversion H. subst. inversion H1. subst. auto.
  - inversion H; subst. inversion H1; subst; simpl; eauto.
    simpl. eauto.
Qed. 


Lemma tick_le_gc s s' : tick_le s s' -> store_le (gc s) (gc s').
Proof.
  intros. destruct H.
  - destruct H;simpl;eauto.
  - simpl. eauto.
Qed.



Definition suffix_le Hs1 Hs3 := exists Hs2, suffix Hs1 Hs2 /\ heapseq_le Hs2 Hs3.

Lemma suffix_skipn Hs1 Hs2 : suffix Hs1 Hs2 -> exists n, Hs1 = skipn n Hs2.
Proof.
  intros. induction H.
  - destruct IHsuffix. exists (S x). simpl. assumption.
  - exists 0. simpl. auto.
Qed.

Lemma heapseq_le_skipn n : forall Hs1 Hs2,  heapseq_le Hs1 Hs2 -> heapseq_le (skipn n Hs1) (skipn n Hs2).
Proof.
  induction n.
  - simpl. auto.
  - intros. destruct Hs1; inversion H;subst;eauto.
Qed.
    
Lemma heapseq_le_suffix Hs1 Hs2 Hs3 :
  heapseq_le Hs1 Hs2 -> suffix Hs3 Hs2 -> exists Hs4, suffix Hs4 Hs1 /\ heapseq_le Hs4 Hs3.
Proof.
  intros. apply suffix_skipn in H0. destruct H0.
  exists (skipn x Hs1). split. apply skip_suffix. subst. eauto using heapseq_le_skipn.
Qed.


Lemma heapseq_le_concat  Hs1 Hs2 Hs3 Hs4 :
  heapseq_le Hs1 Hs2 -> heapseq_le Hs3 Hs4 -> heapseq_le (Hs1 ++ Hs3) (Hs2 ++ Hs4).
Proof. intros. eauto using Forall2_app. Qed.

Lemma suffix_concat Hs1 Hs2 : suffix Hs2 (Hs1 ++ Hs2).
Proof.
  induction Hs1;simpl; eauto.
Qed. 

Lemma heapseq_le_suffix' Hs1 Hs2 Hs3 :
  heapseq_le Hs1 Hs3 -> suffix Hs1 Hs2 ->
  exists Hs4, heapseq_le Hs2 Hs4  /\suffix Hs3 Hs4.
Proof.
  intros HS Su.
  apply suffix_skipn in Su. autodest.
  exists (firstn x Hs2 ++ Hs3). split.
  assert (firstn x Hs2 ++ skipn x Hs2 = Hs2) as SK by eauto using firstn_skipn.
  rewrite <- SK at 1. apply heapseq_le_concat. apply heapseq_le_refl. assumption.
  eauto using suffix_concat.
Qed. 

Lemma tick_le_bot s s' : tick_le s s' -> s = store_bot <-> s' = store_bot.
Proof.
  intro T. split; intros S;subst;inversion T;subst; inversion H; auto.
Qed.

Lemma tick_le_bot' s s' : tick_le s s' -> s <> store_bot <-> s' <> store_bot.
Proof.
  intro T. split;intros S C;subst;inversion T;subst; inversion H; auto.
Qed.


Hint Resolve tick_le_refl store_le_refl heap_le_refl heaps_le_refl heapseq_le_refl .


Lemma tick_le_gc': forall s : store, tick_le (gc s) s.
Proof.
  intros. destruct s;simpl;eauto. destruct o; eauto. 
Qed.


Lemma tick_le_tick' s hn hl  : tick_le (store_lock (Some hn) hl) s ->
                              exists hn' hl', s = store_lock (Some hn') hl' /\
                                              heap_le hn hn' /\ heap_le hl hl'.
Proof.
  intros T. inversion T. subst. inversion H. subst. eauto.
Qed.


Lemma heap_le_empty h : heap_le heap_empty h.
Proof.
  intros l t M. assert (exists t, heap_mapsto l t heap_empty) as C by eauto.
  apply heap_empty_fresh in C. contradiction.
Qed.

Hint Resolve heap_le_empty.

Lemma tick_le_empty h h' : tick_le (store_lock None heap_empty) (store_lock h h').
Proof.
  destruct h; eauto.
Qed.

Lemma tick_le_cons hn hl l t :
  heap_fresh l hl ->
  tick_le (store_lock hn hl) (store_lock hn (heap_cons hl l t)).
Proof.
  intro. constructor. destruct hn ;econstructor; eauto using heap_cons_mono.
Qed.


Lemma wsuffix_trans Hs1 Hs2 Hs3 : wsuffix Hs1 Hs2 -> wsuffix Hs2 Hs3 -> wsuffix Hs1 Hs3.
Proof.
  intros W1 W2. dependent destruction W1. dependent destruction W2.
  apply suffix_skipn in H2. destruct H2 as (n & S1). subst.
  apply suffix_skipn in H0. destruct H0 as (n' & S2). subst.
  apply heapseq_le_skipn with (n:=n') in H1.
  rewrite skipn_skipn in H1. rewrite Nat.add_comm in H1.
  rewrite <- skipn_skipn in H1.
  pose (heapseq_le_trans _ _ _ H1 H) as HL.
  rewrite skipn_skipn in HL.
  econstructor. eassumption. apply skip_suffix.
Qed.

Lemma suffix_wsuffix Hs Hs' : suffix Hs Hs' -> wsuffix Hs Hs'.
Proof.
  intros Su. econstructor;eauto.
Qed.
Lemma heapseq_le_wsuffix Hs Hs' : heapseq_le Hs' Hs -> wsuffix Hs Hs'.
Proof.
  intros Su. econstructor;eauto.
Qed.

Lemma heapseq_le_suffix_trans Hs1 Hs2 Hs3 : wsuffix Hs1 Hs2 -> heapseq_le Hs1 Hs3 -> wsuffix Hs3 Hs2.
Proof.
  intros. eauto using wsuffix_trans, heapseq_le_wsuffix.
Qed.

Lemma heapseq_le_cons_wsuffix H Hs  Hs' : heapseq_le Hs (H :: Hs') -> wsuffix Hs' Hs.
Proof.
  intros L. 
  inversion L. subst.
  econstructor;eauto.
Qed.


(* Other properties of heaps and stores *)

Lemma heap_dom_cons' l h t : heap_dom l (heap_cons h l t).
Proof.
  exists t. apply heap_cons_mapsto_eq. auto.
Qed.

Lemma heap_dom_cons l l' h t : heap_dom l h -> heap_dom l (heap_cons h l' t).
  unfold heap_dom. intro H. destruct H as (u & H).
  pose (Nat.eq_decidable l l') as D. destruct D.
  - subst. apply heap_dom_cons'.
  - exists u. rewrite heap_cons_mapsto_neq; auto. 
Qed.


Lemma heap_dom_alloc_fresh l h : heap_dom l h -> l <> alloc_fresh h.
Proof.
  intros D.
  pose (heap_fresh_alloc h).
  destruct (Nat.eq_decidable l (alloc_fresh h)). subst. contradiction. assumption.
Qed.


Lemma store_mapsto_gc l t s : store_mapsto l t s -> store_mapsto l t (gc s).
Proof.
  intros. destruct H; simpl; autodest.
Qed.
  

Lemma store_tick_gc s h : store_tick (gc s) h = store_tick s h.
Proof.
  destruct s; auto.
Qed.


Lemma gc_idem s : gc (gc s) = gc s.
Proof.
  destruct s;auto.
Qed.


Lemma store_bot_gc s : s <> store_bot <-> gc s <> store_bot.
Proof.
  split; intros; destruct s; intro C;subst;simpl in *; try contradiction; inversion C.
Qed. 


Lemma length_skipn n A  : forall (Hs : list A), n <= length Hs -> length (skipn n Hs) = length Hs - n.
Proof.
  induction n;intros.
  - unfold skipn. simpl. zify;omega.
  - destruct Hs. inversion H. simpl in *. apply IHn. omega.
Qed.

Definition heaps_single (h : heap) : heaps := (fun h' => h' = h).


Lemma heaps_single_le h1 h2 : heap_le h1 h2 -> heaps_le (heaps_single h1) (heaps_single h2).
Proof.
  intros L h HS. inversion HS. subst. eauto. exists h1. split. constructor. assumption.
Qed.



  
Lemma heaps_single_refl h : heaps_single h h.
Proof. constructor. Qed.

Hint Resolve heaps_single_refl.


(* Closed heaps *)

Definition closed_heap (h : heap) := forall l t, heap_mapsto l t h -> closed_term t.

Inductive closed_store : store -> Prop :=
| closed_store_bot : closed_store store_bot
| closed_store_lock h : closed_heap h -> closed_store (store_lock None h)
| closed_store_tick h h' : closed_heap h -> closed_heap h' -> closed_store (store_lock (Some h) h').

Definition closed_heaps (H : heaps) := forall h, H h -> closed_heap h.

Notation closed_heapseq := (Forall closed_heaps).



Lemma closed_heap_cons_rev u h l t : closed_term u -> heap_mapsto l u h -> closed_heap (heap_cons h l t) -> closed_heap h.
Proof.
  intros CT M CH.
  intros l' t' M'.
  destruct (Nat.eq_decidable l l').
  - subst. eapply heap_mapsto_determ in M;eauto. subst. auto.
  - eapply CH. rewrite heap_cons_mapsto_neq; eauto.
Qed.


Hint Constructors closed_store.


Lemma suffix_closed Hs Hs' : closed_heapseq Hs -> suffix Hs' Hs -> closed_heapseq Hs'.
Proof.
  intros C Su. induction Su. inversion C. subst. eauto. auto.
Qed.

Lemma append_closed Hs Hs' : closed_heapseq Hs -> closed_heapseq Hs' -> closed_heapseq (Hs ++ Hs').
Proof.
  intros C1 C2. induction Hs;simpl;eauto. inversion C1. subst. eauto. 
Qed.

Lemma firstn_closed Hs n : closed_heapseq Hs -> closed_heapseq (firstn n Hs).
Proof.
  intros C. generalize dependent Hs. induction n;intros;simpl.
  constructor. destruct Hs. constructor. inversion C. subst. constructor;eauto. 
Qed.


Lemma heapseq_le_suffix'' Hs1 Hs2 Hs3 :
  heapseq_le Hs1 Hs3 -> suffix Hs1 Hs2 -> closed_heapseq Hs2 -> closed_heapseq Hs3 ->
  exists Hs4, heapseq_le Hs2 Hs4  /\suffix Hs3 Hs4 /\ closed_heapseq Hs4.
Proof.
  intros HS Su.
  apply suffix_skipn in Su. autodest.
  exists (firstn x Hs2 ++ Hs3). split.
  assert (firstn x Hs2 ++ skipn x Hs2 = Hs2) as SK by eauto using firstn_skipn.
  rewrite <- SK at 1. apply heapseq_le_concat. apply heapseq_le_refl. assumption.
  split. eauto using suffix_concat.
  eauto using append_closed, firstn_closed.
Qed.

Lemma closed_store_gc s: closed_store s -> closed_store (gc s).
Proof.
  intros CS. destruct CS;simpl;eauto.
Qed.

Lemma closed_heap_empty : closed_heap heap_empty.
Proof.
    intros l t M. assert (exists t, heap_mapsto l t heap_empty) as C by eauto.
  apply heap_empty_fresh in C. contradiction.
Qed. 