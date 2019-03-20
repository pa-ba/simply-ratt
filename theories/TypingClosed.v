From SimplyRatt Require Export Typing ClosedTerms.
From SimplyRatt Require Import Tactics.

From Coq Require Import Omega Program.



(* This module proves that t \gamma is a closed term, given that \Gamma ⊢ t
∶ A and \gamma assigns a closed term to each variable in \Gamma. *)


(* skipping in substitutions *)

Fixpoint sub_skip (n : nat) (g : sub) : sub :=
  match n with
  | 0 => g
  | S n' => match g with
            | _ :: g' => None :: sub_skip n' g'
            | _  => g
            end
  end.

Lemma sub_skip_nil n : sub_skip n nil = nil.
Proof.
  destruct n;auto.
Qed.


Open Scope nat.

Lemma sub_lookup_skip_above i s g :
  i >= s -> 
 sub_lookup (sub_skip s g) i = sub_lookup g i.
Proof.
  intros. generalize dependent i. generalize dependent g. 
  induction s;intros.
  - auto.
  - assert (exists j, i = S j /\ j >= s) as P by (exists (pred i); zify;omega).
    autodest. destruct g;auto. destruct o;simpl; repeat rewrite sub_lookup_succ; eauto.
Qed.

Lemma sub_lookup_skip_below i s g :
  i < s -> 
 sub_lookup (sub_skip s g) i = None.
Proof.
  intros. generalize dependent i. generalize dependent g. 
  induction s;intros.
  - inversion H.
  - destruct g; simpl; destruct i;auto.
    rewrite sub_lookup_succ. apply IHs. omega.
Qed.


(* The predicate svars s b t indicates that t contains no variables i
   with b+s > i >= b *)

Inductive svars (s : index) : index -> term -> Prop :=
| svars_var_above b i : i >= b + s -> svars s b (var i)
| svars_var_below b i : i < b -> svars s b (var i)
| svars_unit b : svars s b unit
| svars_natlit b n : svars s b (natlit n)
| svars_abs b t : svars s (S b) t -> svars s b (abs t)
| svars_app b t1 t2 : svars s b t1 -> svars s b t2 -> svars s b (app t1 t2)
| svars_pair b t1 t2 : svars s b t1 -> svars s b t2 -> svars s b (pair t1 t2)
| svars_pr1 b t : svars s b t -> svars s b (pr1 t)
| svars_pr2 b t : svars s b t -> svars s b (pr2 t)
| svars_in1 b t : svars s b t -> svars s b (in1 t)
| svars_in2 b t : svars s b t -> svars s b (in2 t)
| svars_case b t t1 t2 : svars s b t ->  svars s (S b) t1 -> svars s (S b) t2 -> svars s b (case t t1 t2)
| svars_delay b t : svars s b t -> svars s b (delay t)
| svars_adv b t : svars s b t -> svars s b(adv t)
| svars_ref b l : svars s b (ref l)
| svars_box b t : svars s b t -> svars s b (box t)
| svars_unbox b t : svars s b t -> svars s b (unbox t)
| svars_progr b t : svars s b t -> svars s b (progr t)
| svars_promote b t : svars s b t -> svars s b (promote t)
| svars_into b t : svars s b t -> svars s b (into t)
| svars_out b t : svars s b t -> svars s b (out t)
| svars_fixp b t : svars s (S b) t -> svars s b (fixp t).

Hint Constructors svars.


Lemma sub_skips_id' b s g t :
  svars s b t ->
  sub_app (sub_skip (b+s) g) t = sub_app (sub_skip b g) t.
Proof.
  intros SV. generalize dependent g.
  induction SV;intros;
    try solve[simpl; try first [rewrite IHSV1, IHSV2|rewrite IHSV] ; reflexivity].
  - simpl. repeat rewrite sub_lookup_skip_above by omega. auto.
  - simpl. repeat rewrite sub_lookup_skip_below by omega. auto.
  - simpl. pose (IHSV (None :: g)) as IH. simpl in IH. rewrite IH. reflexivity.
  - pose (IHSV2 (None :: g)) as IH2. pose (IHSV3 (None :: g)) as IH3.
    simpl in IH2, IH3. simpl. rewrite IHSV1, IH2, IH3. reflexivity.
  - simpl. pose (IHSV (None :: g)) as IH. simpl in IH. rewrite IH. reflexivity.
Qed.

Lemma sub_skips_id s g t : svars s 0 t -> sub_app (sub_skip s g) t = sub_app g t.
Proof.
  intros SV. eapply sub_skips_id' in SV. simpl in SV. rewrite SV. reflexivity.
Qed.


(* skipping in contexts *)

Inductive ctx_skips : forall {ty}, index -> index -> ctx ty -> Prop :=
| ctx_skips_empty s b : ctx_skips s b ctx_empty
| ctx_skips_var {ty} (G : ctx ty) A s b : ctx_skips s b G -> ctx_skips s (S b) (ctx_var G A)
| ctx_skips_var' {ty} (G : ctx ty) A : ctx_skips 0 0 G -> ctx_skips 0 0 (ctx_var G A)
| ctx_skips_skip {ty} (G : ctx ty) s : ctx_skips (pred s) 0 G -> ctx_skips s 0 (ctx_skip G)
| ctx_skips_skip' {ty} (G : ctx ty) s b : ctx_skips s b G -> ctx_skips s (S b) (ctx_skip G)
| ctx_skips_lock G s b : ctx_skips s b G -> ctx_skips s b (ctx_lock G)
| ctx_skips_tick G s b : ctx_skips s b G -> ctx_skips s b (ctx_tick G).


Hint Constructors ctx_skips.


Lemma ctx_lookup_skips ty (G : ctx ty) : forall n T s b,
  ctx_lookup G n T -> ctx_skips s b G -> n < b \/ n >= b + s.
Proof.
  induction G;intros n T s B L SK.
  - inversion L.
  - inversion SK;subst. dependent destruction H.
    destruct n. inversion L. left. zify;omega.
    inversion L. subst. dependent destruction H.
    eapply IHG with (b := b) (n := n) (s := s) in H4;eauto.
    destruct H4;omega.
    right;zify;omega.
  - destruct n; inversion L. dependent destruction H.
    inversion SK;subst; dependent destruction H;
    eapply IHG in H1;eauto;
      destruct H1;zify;omega.
  - inversion L.
  - inversion L.
Qed. 

Lemma ctx_skips_later s b G : ctx_skips s b G ->
                              ctx_skips s b (skip_later G).
Proof.
  intros.  generalize dependent b. generalize dependent s.
  dependent induction G;intros;inversion H; dependent destruction H0; subst; simpl; eauto.
Qed.

Lemma ctx_skips_now s b G : ctx_skips s b G ->
                              ctx_skips s b (skip_now G).
Proof.
  intros.  generalize dependent b. generalize dependent s.
  dependent induction G;intros;inversion H; dependent destruction H0; subst; simpl; eauto.
Qed.



Lemma typing_svars ty (G : ctx ty) s b t A : ctx_skips s b G -> G ⊢ t ∶ A -> svars s b t.
Proof.
  intros SK T. generalize dependent b.
  induction T;intros;
    try solve[constructor;eauto using ctx_skips_later,ctx_skips_now].
  - eapply ctx_lookup_skips in H;eauto. destruct H;auto.
Qed.

(* calculates how many context items are skipped by skip_now *)

Fixpoint skip_now_count (G : ctx now) : nat :=
  match G with
  | ctx_lock G' => 0
  | @ctx_var now G' _ => S (skip_now_count G')
  | @ctx_skip now G' => S (skip_now_count G')
  end.

(* calculates how many context items are skipped by skip_later *)

Fixpoint skip_later_count (G : ctx later) : nat :=
  match G with
  | ctx_tick G' => 0
  | @ctx_var later G' _ => S (skip_later_count G')
  | @ctx_skip later G' => S (skip_later_count G')
  end.


Lemma ctx_skips_0 ty (G : ctx ty) : forall b, ctx_skips 0 b G.
Proof.
  induction G;intros;eauto.
  - destruct b; eauto.
  - destruct b; eauto.
Qed.

Lemma skip_now_skipn G : ctx_skips (skip_now_count G) 0 (skip_now G).
Proof.
  dependent induction G;intros;simpl; eauto using ctx_skips_0.
Qed.

Lemma skip_later_skipn G : ctx_skips (skip_later_count G) 0 (skip_later G).
Proof.
  dependent induction G;intros;simpl; eauto using ctx_skips_0.
Qed.


(* Proof that well-typed terms can be turned into closed terms by as
suitable substitution as defined by the predicate ground_sub below. *)

Inductive ground_sub : forall {ty}, index -> sub -> ctx ty -> Prop :=
| ground_sub_empty : ground_sub 0 nil ctx_empty
| ground_sub_var_0 ty (G : ctx ty) g t A :
    ground_sub 0 g G -> ground_sub 0 (Some t :: g) (ctx_var G A)
| ground_sub_var_succ ty (G : ctx ty) i g A x :
    ground_sub i g G -> ground_sub (S i) (x :: g) (ctx_var G A)
| ground_sub_skip_0 ty (G : ctx ty) g x :
    ground_sub 0 g G -> ground_sub 0 (x :: g) (ctx_skip G)
| ground_sub_skip_succ ty (G : ctx ty) i g x :
    ground_sub i g G -> ground_sub (S i) (x :: g) (ctx_skip G)
| ground_sub_tick G i g  :
    ground_sub i g G -> ground_sub i g (ctx_tick G)
| ground_sub_lock G i g  :
    ground_sub i g G -> ground_sub i g (ctx_lock G)
.

Hint Constructors ground_sub.

Lemma ground_sub_later b g G : ground_sub b g G -> ground_sub b g (skip_later G).
Proof.
  intros Gr. dependent induction Gr;simpl;auto.
Qed.


Lemma ground_sub_now b g G : ground_sub b g G -> ground_sub b g (skip_now G).
Proof.
  intros Gr. dependent induction Gr;simpl;auto.
Qed.

Hint Resolve ground_sub_later ground_sub_now.

Lemma ground_sub_nth ty b g (G : ctx ty) i T :
  ctx_lookup G i T -> ground_sub b g G -> i < b \/ exists t, sub_lookup g i = Some t.
Proof.
  intros L GS. generalize dependent b. generalize dependent g. 
  induction L;intros.
  - dependent destruction GS.
    + right. eexists. cbv. reflexivity.
    + left. zify;omega.
  - dependent destruction GS. 
    + right. apply IHL in GS. destruct GS.
      inversion H. autodest.
    + apply IHL in GS. autodest. left. omega.
  - dependent destruction GS.
    + right. apply IHL in GS. destruct GS.
      inversion H.  autodest.
    + apply IHL in GS. autodest. left. omega.
Qed.


Lemma ground_sub_closed ty g (G : ctx ty) A t b :
      G ⊢ t ∶ A -> closed_sub g -> ground_sub b g G -> fvars b (sub_app g t).
Proof.
  intros T C Gr. generalize dependent g. generalize dependent b.
  induction T;intros;simpl;eauto.
  - assert(x < b \/ exists t, sub_lookup g x = Some t) as L by eauto using ground_sub_nth.
    destruct L.
    + remember (sub_lookup g x) as N. symmetry in HeqN.
      destruct N. eauto using sub_lookup_closed, closed_fvars.
      eauto.
    + destruct H0. rewrite H0. eauto using sub_lookup_closed, closed_fvars.
     

  - constructor. apply IHT1;eauto. apply IHT2;eauto. apply IHT3;eauto.
  - constructor. apply IHT;eauto.
Qed.

Lemma typed_closed A t :
      ctx_empty ⊢ t ∶ A -> closed_term t.
Proof.
  intros T. eapply ground_sub_closed in T;eauto. rewrite sub_empty_app in T;eauto.
Qed.

(* Other lemmas. *)

Lemma sub_skip_closed g n : closed_sub g -> closed_sub (sub_skip n g).
Proof.
  intros. generalize dependent g. induction n;intros.
  - auto.
  - simpl in *. destruct g;eauto.
    inversion H;subst; eauto.
Qed.
