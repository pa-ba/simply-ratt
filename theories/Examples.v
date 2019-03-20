From SimplyRatt Require Import Typing Worlds. 

(* Typing examples *)


Example id_wt ty A (G : ctx ty) : ty <> later ->
    G ⊢ abs (var 0) ∶ (Arrow A A). 
Proof.
  eauto.
Qed. 


Example id_app_closed ty t A (G : ctx ty) :
  ty <> later ->
  G ⊢ t ∶ A ->
  G ⊢ app (abs (var 0)) t ∶ A.
Proof.
  eauto.
Qed. 

Lemma now_not_later : now <> later.
Proof.
  intros C; inversion C.
Qed.

Lemma init_not_later : init <> later.
Proof.
  intros C; inversion C.
Qed.

Hint Resolve now_not_later init_not_later id_wt.



Example box_id_closed (G : ctx init)  A :
    G ⊢ box (abs (var 0)) ∶ Box (Arrow A A).
Proof.
  auto.
Qed. 


Notation  Str := (Mu (Times Nat (TypeVar 0))). 

Example wf_str : closed_type Str.
Proof.
 autounfold.  eauto.
Qed. 


Notation const_str := (fixp (into (pair (natlit 0) (var 0)))).

Example const_str_wt (G : ctx init) : 
    G ⊢ const_str ∶ Box Str. 
Proof.
  repeat constructor.
Qed.

Definition str_unfold : Times Nat (Delay Str) = tsubst 0 (Times Nat (TypeVar 0)) (Delay Str). 
Proof. 
  reflexivity. 
Qed.


    

Notation head := (abs (pr1 (out (var 0)))).

Example head_wt ty (G : ctx ty) :
  ty <> later ->
  G ⊢ head ∶ (Arrow Str Nat). 
Proof.
  repeat econstructor. eauto. reflexivity.
Qed. 

Notation const_str_head := (app head (unbox const_str)).

Example const_str_head_wt (G : ctx now) :
    G ⊢ const_str_head ∶ Nat. 
Proof.
  repeat econstructor. eauto. apply str_unfold.
  simpl. eauto.
Qed.

Notation tail := (abs (pr2 (out (var 0)))).

Definition tail_wt ty (G : ctx ty)  :
  ty <> later ->
  G ⊢ tail ∶ Arrow Str (Delay Str).
Proof.
  repeat econstructor;eauto.
Qed. 

                               
Notation str_map  :=
  (abs (fixp (abs (into (pair ((app (unbox (var 2))) (app head (var 0))) (delay ((app (adv (var 1)) (adv (app tail (var 0))))))))))).

Example str_map_wf (G : ctx init) : 
    G ⊢ str_map ∶ (Arrow (Box (Arrow Nat Nat)) (Box (Arrow Str Str))). 
Proof.
  repeat econstructor;eauto. 
Qed. 

Notation str_filter := (abs (abs (fixp (abs (into (pair( case (app (unbox (var 3)) (app head (var 0))) (app head (var 1)) (promote (var 3))) (delay (app (adv (var 1)) (adv (app tail (var 0))))))))))). 
Example str_filter_wt (G : ctx init) :
  G ⊢ str_filter ∶ Arrow (Box(Arrow Nat (Plus Unit Unit))) (Arrow Nat (Box(Arrow Str Str))). 
Proof.
  repeat econstructor;eauto. 
Qed. 

Notation str_alternate := (fixp (abs (abs (into (pair (app head (var 1)) (delay (app ((app (adv (var 2)) (adv (app tail (var 1))))) (adv (app tail (var 0)))))))))). 


Example str_alternate_wt (G : ctx init) :
  G ⊢ str_alternate ∶ Box(Arrow Str (Arrow Str Str)). 
Proof.
  repeat econstructor;eauto. 
Qed. 

Notation Bool := (Plus Unit Unit). 
Notation Clock := (Mu (Times Bool (TypeVar 0))). 



Notation clock_alternate  := (fixp (abs (abs (into (pair (app (abs (pr1 (out (var 0)))) (var 1)) (delay (app ((app (adv (var 2)) (adv (app (abs (pr2 (out (var 0)))) (var 1))))) (adv (app (abs (pr2 (out (var 0)))) (var 0)))))))))). 

Example clock_alternate_wt (G : ctx init) :
  G ⊢ clock_alternate ∶ Box (Arrow Clock (Arrow Clock Clock)). 
Proof.
  repeat econstructor;eauto. 
Qed. 

Notation always := (fixp (into (pair (in1 unit) (delay (adv (var 0)))))). 

Example always_wt (G : ctx init) : G ⊢ always ∶ Box Clock. 
Proof.
  repeat econstructor;eauto. 
Qed. 

Notation never := (fixp (into (pair (in2 unit) (delay (adv (var 0)))))). 
Example never_wt (G : ctx init)  : G ⊢ never ∶ Box Clock. 
Proof.
  repeat econstructor;eauto. 
Qed. 

Notation half_step := (box (app (app (unbox clock_alternate) (unbox always)) (unbox never))). 
Example half_step_wt (G : ctx init) : G ⊢ half_step ∶ Box Clock. 
Proof.
  repeat econstructor;eauto. simpl.
  instantiate (1 := Times Bool (TypeVar 0)). reflexivity.
  reflexivity. instantiate (1 := Times Bool (TypeVar 0)). reflexivity.
  repeat constructor.
  repeat constructor.
Qed.

Notation on_tick := (fixp (abs (abs (into (pair (case (app head (var 0)) (app head (var 2)) (natlit 0)) (delay (app ((app (adv (var 2))) (adv (app tail (var 1)))) (adv (app tail (var 0)))))))))). 
Example on_tick_wt (G : ctx init) :
  G ⊢ on_tick ∶ Box(Arrow Str (Arrow Clock Str)). 
Proof.
  repeat econstructor;eauto; reflexivity. 
Qed. 

           


        
        



  

  
