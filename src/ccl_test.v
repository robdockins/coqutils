Require Import ccl.

Definition asdf (f:nat -> nat -> nat) := True.
Fixpoint iter (n:nat) (f: nat -> nat) : nat -> nat :=
  match n with
  | O => fun x => x
  | Datatypes.S n' => fun x => f (iter n' f x)
  end.

Tactic Notation "ccl_test" constr(t) := (CCL.ccl_test t).

Goal True.
  ccl_test (fun w w' => plus (plus w (1+1+1+1))
               (iter w' (fun x => x*4 + 3) w)).
  reflexivity.

  ccl_test (fun (w:nat) (q:bool) => w).
  reflexivity.

  ccl_test (fun (w:nat) (q:bool) => plus w).
  reflexivity.

  ccl_test (fun q:nat => q).
  reflexivity.

  ccl_test (fun w => plus w (snd (10,5))).
  reflexivity.

  ccl_test (fun w w' => w+w').
  reflexivity.

  ccl_test (fun w => Datatypes.S w).
  reflexivity.
  
  ccl_test 5. 
  reflexivity.

  ccl_test (fun w => iter w (fun x => x + 3)).
  reflexivity.

  trivial.
Qed.
Print Unnamed_thm.

Goal (asdf (fun w w' => plus (plus w (1+1+1+1)) 
               (iter w' (fun x => x*4 + 3) w))).
  cut (asdf (fun w => iter w (fun x => x + 3))).
  intro H.

  cut (asdf (fun w w' => w + (fix q w' : nat := match w' with 0 => w | S n => 3 + q n end) w')).
  intro H0.

  ccl in H0.
  unccl in H0.

  ccl in H.
  ccl.

  unccl.
  unccl in H.

  hnf. trivial.
  hnf. trivial.
  hnf. trivial.
Qed.
Print Unnamed_thm0.
