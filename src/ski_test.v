Require Import ski.

Definition asdf (f:nat -> nat -> nat) := True.
Fixpoint iter (n:nat) (f: nat -> nat) : nat -> nat :=
  match n with
  | O => fun x => x
  | Datatypes.S n' => fun x => f (iter n' f x)
  end.

Goal (asdf (fun w w' => plus (plus w (1+1+1+1)) 
               (iter w' (fun x => x*4 + 3) w))).
  cut (asdf (fun w => iter w (fun x => x + 3))).
  intro H.

  cut (asdf (fun w w' => w + (fix q w' : nat := match w' with 0 => w | S n => 3 + q n end) w')).
  intro H0.

  (*ski in H0.*) (*fails, cant SKI through fixpoints *)
  
  ski in H.
  ski.

  hnf. trivial.
  hnf. trivial.
  hnf. trivial.
Qed.
Print Unnamed_thm. (* lots of junk...*)
