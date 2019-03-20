From SimplyRatt Require Export Reduction.

From SimplyRatt Require Import Tactics.

From Coq Require Import Omega.

Fixpoint tsize (A : type) : nat :=
  match A with
  | Unit => 1
  | Nat => 1
  | TypeVar _ => 1
  | Arrow B C => S (tsize B + tsize C)
  | Plus B C => S (tsize B + tsize C)
  | Times B C => S (tsize B + tsize C)
  | Delay B => 1
  | Box B => S (tsize B)
  | Mu B => S (tsize B)
  end.

Lemma tsize_subst i A B :  tsize (tsubst i A (Delay B)) = tsize A.
Proof.
  generalize dependent i. generalize dependent B. induction A;intros;simpl; eauto.
  - destruct (i0 =? i); eauto.
Qed.

(* Definition of logical relation *)

Fixpoint vreln (n : nat) {struct n} : type -> nat -> heapseq -> store -> term -> Prop :=
  fix vreln' (A : type) (N: nat) (Hs : heapseq) (s : store) (t : term) {struct N}  : Prop :=
    match A, N with
    | Arrow B C, S M => exists t', t = abs t' /\
      forall Hs' s', heapseq_le Hs Hs' -> store_le (gc s) s' -> closed_heapseq Hs' -> closed_store s' ->
      forall v, vreln' B (M - tsize C) Hs' s' v -> closed_term v ->
      forall Hs'' s'', heapseq_le Hs' Hs'' -> tick_le s' s'' -> closed_heapseq Hs'' -> closed_store s'' ->
      exists w s''', {sub_term t' v, s''} ⇓ {w, s'''} /\
                           vreln' C (M - tsize B) Hs'' s''' w
    | Mu B, S M => exists v, t = into v /\
                            vreln' (tsubst 0 B (Delay (Mu B))) M Hs s v
    | Delay B, _ => 
      match n with
      | O => False  
      | 1  => exists l, t = ref l
      | S n' => exists l H (Hs' : heapseq), t = ref l /\ Hs = H :: Hs' /\
                    exists u, store_mapsto l u s /\ forall h, H h -> 
                    forall Hs'' s', heapseq_le Hs' Hs'' -> tick_le (store_tick s h) s' -> closed_heapseq Hs'' -> closed_store s' ->
                    exists w s'', {u, s'} ⇓ {w, s''} /\ vreln n' B (tsize B) Hs'' s'' w
                  end
    | Box B, S M =>
      match n with
      | O => False
      | S m =>
      (forall n', S n' <= m ->
           (forall Hs'' s', heapseq_le (skipn (S n') Hs) Hs'' -> tick_le (store_lock None heap_empty) s' ->
                            closed_heapseq Hs'' -> closed_store s' ->
                            exists v s'', {unbox t, s'} ⇓ {v, s''} /\ vreln (m - n') B M Hs'' s'' v)) /\
            (forall Hs' s', heapseq_le Hs Hs' -> tick_le (store_lock None heap_empty) s' ->
                            closed_heapseq Hs' -> closed_store s' ->
                            exists v s'', {unbox t, s'} ⇓ {v, s''} /\ vreln' B M Hs' s'' v) /\
            isvalue t
      end
    | TypeVar i, _  => False
    | Unit, _ => t = unit
    | Nat, _ => exists n, t = natlit n
    | Plus B C, S M => (exists v, t = in1 v /\ vreln' B (M - tsize C) Hs s v)
                  \/ (exists v, t = in2 v /\ vreln' C (M - tsize B) Hs s v)
    | Times B C, S M => exists v1 v2, t = pair v1 v2 /\ vreln' B (M - tsize C) Hs s v1
                                       /\ vreln' C (M - tsize B) Hs s v2
    | _, _ => False
    end.


(* Below are the actual definitions that we are working with: vrel and trel *)

Definition vrel A Hs s t := vreln (S (length Hs)) A (tsize A) Hs s t.

Definition trel (A : type) (Hs : heapseq) (s : store) (t : term) : Prop :=
  forall Hs' s', heapseq_le Hs Hs' -> tick_le s s' ->
                 closed_heapseq Hs' -> closed_store s' -> exists v s'',
                     {t, s'} ⇓ {v, s''} /\ vrel A Hs' s'' v.


(* Below we give characterisations of vrel so that we don't need to
   work with vreln. *)

Lemma vrel_plus A B Hs s t : vrel (Plus A B) Hs s t <->
                               (exists v, t = in1 v /\ vrel A Hs s v)
                               \/ (exists v, t = in2 v /\ vrel B Hs s v).
Proof.
  assert (tsize A + tsize B - tsize B = tsize A) as SA by omega.
  assert (tsize A + tsize B - tsize A = tsize B) as SB by omega.
  unfold vrel. simpl.
  - split;intro. 
    * do 3 destruct H.
      + left. rewrite SA in *. exists x. split;eauto.
      + right. rewrite SB in *. exists x. split;eauto.
    * do 3 destruct H.
      + left. rewrite SA in *. exists x. split;eauto.
      + right. rewrite SB in *. exists x. split;eauto.
Qed.

Lemma vrel_times A B Hs s t : vrel (Times A B) Hs s t <->
                                exists v1 v2, t = pair v1 v2 /\ vrel A Hs s v1
                                       /\ vrel B Hs s v2.
Proof.
  assert (tsize A + tsize B - tsize B = tsize A) as SA by omega.
  assert (tsize A + tsize B - tsize A = tsize B) as SB by omega.
  unfold vrel. simpl.
  - split;intro. 
    * do 3 destruct H. destruct H0.
      + rewrite SA in *. rewrite SB in *.  exists x, x0. split;eauto.
    * do 3 destruct H. destruct H0.
      + rewrite SA in *. rewrite SB in *.  exists x, x0. split;eauto. 
Qed.


Lemma vrel_mu A Hs s t : vrel (Mu A) Hs s t <->
                           exists v, t = into v /\ vrel (tsubst 0 A (Delay (Mu A))) Hs s v.
Proof.
  unfold vrel. rewrite tsize_subst. simpl; split; intros.
  - do 2 destruct H. exists x. split; eauto.
  - do 2 destruct H. exists x. split; eauto.
Qed.


Lemma vrel_val : forall A Hs s t, vrel A Hs s t -> isvalue t.
Proof.
  intro A. remember (tsize A) as N. generalize dependent A.
  induction (lt_wf N) as [N _ IH]. intro A.
  destruct A;intros;
    try solve[unfold vrel in *; destruct (length Hs);subst; simpl in H; autodest].
  - rewrite vrel_times in H. autodest. constructor.
    + eapply IH with (y := tsize A1). simpl. omega. reflexivity. eassumption.
    + eapply IH with (y := tsize A2). simpl. omega. reflexivity. eassumption.
  - rewrite vrel_plus in H. autodest;constructor.
    + eapply IH with (y := tsize A1). simpl. omega. reflexivity. eassumption.
    + eapply IH with (y := tsize A2). simpl. omega. reflexivity. eassumption.
  - rewrite vrel_mu in H. autodest. constructor.
    eapply IH with (y := tsize (tsubst 0 A (Delay (Mu A)))).
    rewrite tsize_subst. simpl. omega. reflexivity. eassumption.
Qed.  
      

Lemma vrel_delay A H Hs s t :
  vrel (Delay A) (H :: Hs) s t <->
  exists l u, t = ref l /\ store_mapsto l u s /\
              forall h, H h -> trel A Hs (store_tick s h) u.
Proof.
  unfold vrel. split;simpl;intros.
  - autodest. exists x, x2. split. reflexivity. split. assumption.
    intros. unfold trel. intros. inversion H1. subst. remember (H3 h H0 Hs' s' H4 H5 H6 H7) as As.
    autodest. exists x3, x4. split. assumption. unfold vrel.
    assert (length x1 = length Hs') as L1 by eauto using heapseq_le_len.
    rewrite <- L1.  simpl.  assumption.
  - autodest. exists x, H, Hs. split. reflexivity. split. reflexivity.
    exists x0. split. assumption. intros. remember (H2 h H0) as As. unfold trel in As.
    remember (As Hs'' s' H3 H4 H5 H6) as As2. autodest. exists x1, x2. split. assumption. unfold vrel in *.
    assert (length Hs = length Hs'') as L1 by eauto using heapseq_le_len. clear HeqAs2. rewrite <- L1 in v.
    assumption.
Qed.

Lemma vrel_box A Hs s t :
  vrel (Box A) Hs s t <-> (isvalue t /\
                          forall Hs', suffix Hs' Hs -> trel A Hs' (store_lock None heap_empty) (unbox t)).
Proof.
  unfold vrel. split;intros.
  - simpl in *. autodest. split. assumption. unfold trel. intros. inversion H2;subst.
    + assert (S (length Hs'1 - length Hs') <= length (H7 :: Hs'1)) as L1 by (simpl; omega).
      assert (heapseq_le (skipn (length Hs'1 - length Hs') Hs'1) Hs'0) as L2 by (rewrite suffix_length_skip; assumption).
   
      remember (H (length Hs'1 - length Hs') L1 Hs'0 s' L2 H4 H5 H6). clear Heqe H. autodest.
      exists x, x0. split. assumption.
      assert (length (H7 :: Hs'1) - (length Hs'1 - length Hs') = S (length Hs')) as L3.
      assert (length (H7 :: Hs'1) = S (length Hs'1)) as L by reflexivity. rewrite L. apply suffix_length in H8. omega.
      rewrite L3 in *. apply heapseq_le_len in H3. rewrite H3 in *. assumption.
    + remember (H0 Hs'0 s' H3 H4 H5 H6) as As. clear HeqAs H0.  autodest.
      exists x, x0. split. assumption. unfold vrel. apply heapseq_le_len in H3. rewrite <- H3. assumption.
  - autodest. split.
    + intros.
      assert (suffix (skipn (S n') Hs) Hs) as L1 by apply skip_suffix.
      unfold trel in H0.
      remember (H0 (skipn (S n') Hs) L1 Hs'' s' H2 H3 H4 H5) as As. clear HeqAs H0.
      autodest. exists x, x0. split. assumption.
      unfold vrel in H6. apply heapseq_le_len in H2. rewrite length_skipn in H2 by assumption.
      rewrite <- H2 in *.  assert (S (length Hs - S n') = length Hs - n') as L2 by omega.
      rewrite <- L2. assumption.
    + split. intros. unfold trel in H0.
      remember (H0 Hs (suffix_refl _) Hs' s' H1 H2 H3 H4) as As. clear HeqAs H0. autodest.
      exists x, x0. split. assumption. apply heapseq_le_len in H1. unfold vrel in *. rewrite <- H1 in *. assumption.
      assumption.
Qed.

Lemma vrel_arrow A B Hs s t :
  vrel (Arrow A B) Hs s t <-> (exists u, t = abs u /\
     forall Hs' s', heapseq_le Hs Hs' -> store_le (gc s) s' -> closed_heapseq Hs' -> closed_store s' ->
                    forall v, vrel A Hs' s' v -> closed_term v -> trel B Hs' s' (sub_term u v)).
Proof.
  assert (tsize A = tsize A + tsize B - tsize B) as L1 by omega.
  assert (tsize B = tsize A + tsize B - tsize A) as L3 by omega.
  unfold vrel. split;intros.
  - simpl in *. autodest. exists x. split. reflexivity. unfold trel. intros.
    assert (length Hs = length Hs') as L2 by eauto using heapseq_le_len.
    rewrite L1 in H4. rewrite <- L2 in H4. 
    remember (H0 Hs' s' H H1 H2 H3 v H4 H5 Hs'0 s'0 H6 H7 H8 H9) as As. clear HeqAs H0.
    autodest. exists x0, x1. split. assumption.
    unfold vrel. rewrite L3. apply heapseq_le_len in H6. rewrite <- H6. rewrite <- L2. assumption.
  - simpl in *. autodest. exists x. split. reflexivity. intros.
    assert (length Hs = length Hs') as L2 by eauto using heapseq_le_len.
    rewrite <- L1 in H4. rewrite L2 in H4. unfold trel in H0.
    remember (H0 Hs' s' H H1 H2 H3 v H4 H5 Hs'' s'' H6 H7 H8 H9) as As. clear HeqAs H0 H2.
    autodest. exists x0, x1. split. assumption.
    apply heapseq_le_len in H6. rewrite L2. rewrite H6. rewrite <- L3. assumption.
Qed. 

Lemma vrel_unit Hs s t :
  vrel Unit Hs s t <-> t = unit.
Proof.
  unfold vrel in *. intros. split;auto.
Qed.


Lemma vrel_nat Hs s t :
  vrel Nat Hs s t <-> exists n, t = natlit n.
Proof.
  unfold vrel in *. intros. split;auto.
Qed.

Lemma vrel_var i Hs s t :
  vrel (TypeVar i) Hs s t <-> False.
Proof.
    unfold vrel in *. intros. split;auto.
Qed.

Lemma vrel_delay_nil A s t :
  vrel (Delay A) nil s t <-> exists l, t = ref l.
Proof.
  unfold vrel in *. intros. split;auto.
Qed .

Hint Rewrite vrel_delay_nil vrel_delay vrel_var vrel_nat vrel_unit vrel_times vrel_plus vrel_arrow vrel_box vrel_mu : vrel.


Import ListNotations.

Inductive crel : forall {ty}, ctx ty -> heapseq -> store -> sub -> Prop :=
| crel_empty Hs : crel ctx_empty Hs store_bot nil
| crel_var ty (G : ctx ty) Hs s g A t : vrel A Hs s t -> crel G Hs s g ->
                           crel (ctx_var G A) Hs s (Some t :: g)
| crel_skip ty (G : ctx ty) Hs s g : crel G Hs s g ->
                              crel (ctx_skip G) Hs s (None :: g)
| crel_lock G Hs Hs' s g :
    suffix Hs Hs' -> closed_heapseq Hs' -> s <> store_bot ->
    crel G Hs' store_bot g ->
    crel (ctx_lock G) Hs s g
| crel_tick G Hs g hl hn  : 
    crel G (heaps_single hl ::Hs) (store_lock None hn) g ->
    crel (ctx_tick G) Hs (store_lock (Some hn) hl) g
.

Hint Constructors crel.