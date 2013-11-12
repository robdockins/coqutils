(* Robert Dockins (c) 2013. *)

Delimit Scope ski_scope with ski.
Open Scope ski_scope.

Module SKI.

(* Standard SKI combinators and Turner's B and C *)
Definition S A B C (f:A -> B -> C) (g:A -> B) (a:A) : C
  := (f a) (g a).
Definition K A B (a:A) (b:B) := a.
Definition I A (a:A) : A := a.

Definition B A B C (f:B -> C) (g:A -> B) x := f (g x).
Definition C A B C (f:A -> B -> C) (x:B) (y:A) := f y x.

Arguments S {A} {B} {C} f%ski g%ski a%ski.
Arguments K {A} {B} a%ski b%ski.
Arguments I {A} a%ski.
Arguments B {A} {B} {C} f%ski g%ski x%ski.
Arguments C {A} {B} {C} f%ski x%ski y%ski.

Lemma SKxKy A B C (x:B->C) (y:B) :
  S (A:=A) (K x) (K y) = K (x y).
Proof. reflexivity. Qed.

Lemma SSKKxy A B C (x:A->B) (y:A->C) :
  S (S (K K) x) y = x.
Proof. reflexivity. Qed.

Lemma SSSKSxyz A B C D (x:A->B->C->D) (y:A->B->C) (z:A->B) :
  S (S (S (K S) x) y) z = S (S x z) (S y z).
Proof. reflexivity. Qed.

Lemma SKxI A B (x:A->B) : 
  @S A A B (K x) I = x.
Proof. reflexivity. Qed.

Set Printing All.
Lemma SSSKSxyz' A B C D x y z :
  S (S (S (@K _ B (@S A D C)) x) y) z =
  @S B D C (S x z) (@S B A D y z).
Proof. reflexivity. Qed.
 
(* Examine the term t, looking for a variety of simplifications.
   These include redex rules for each combinator and a variety
   of different eta contractions and other identities.
 *)
Ltac do_ski_simpl t k :=
   match t with
    | appcontext G [ @S ?A ?B ?C (K ?f) (K ?x) ] =>
        let G' := context G [(@K C A (f x))] in k G'

    | appcontext G [ @S ?A _ _ K _ ] =>
        let G' := context G [@I A] in k G'

    | appcontext G [ @S ?A ?B _ K] =>
        let G' := context G [@K (A->A) (A->B) (@I A)] in k G'

    | appcontext G [ S (K ?x) ?y ] =>
        let G' := context G [ B x y ] in k G'

    | appcontext G [ S ?x (K ?y) ] =>
        let G' := context G [ C x y ] in k G'

    | appcontext G [ S (K ?f) I ] =>
        let G' := context G [f] in k G'

    | appcontext G [ B (K ?x) ?y ] =>
        let G' := context G [K x] in k G'

    | appcontext G [ B ?x (K ?y) ] =>
        let G' := context G [K (x y)] in k G'

    | appcontext G [ B ?x I ] =>
        let G' := context G [x] in k G'

    | appcontext G [ B I ?x ] =>
        let G' := context G [x] in k G'

    | appcontext G [ S ?f ?g ?x ] =>
        let G' := context G [(f x) (g x)] in k G'

    | appcontext G [ B ?f ?g ?x ] =>
        let G' := context G [f (g x)] in k G'

    | appcontext G [ C ?f ?x ?y ] =>
        let G' := context G [f y x] in k G'

    | appcontext G [ K ?x ?y ] =>
        let G' := context G [x] in k G'

    | appcontext G [ I ?x ] =>
        let G' := context G [x] in k G'

    end.

(* Continue applying reduction rules until no more are found.
   Then enter the continuation.
 *)
Ltac ski_simpl_loop t k :=
  try (do_ski_simpl t ltac:(fun t' => ski_simpl_loop t' k))
    || k t.

(* Check if t contains x, fail if so *)
Ltac check_not_contains x t :=
  match t with
  | appcontext[ x ] => fail 1
  | _ => idtac
  end.

(* SKI convert term 't' with respect to variable 'x'.
   Return the answer into continuation 'k'.

   Note: do_ski and start_ski are mutually recursive.
 *)
Ltac do_ski x t k :=
 let X := type of x in
 ( check_not_contains x t;

      (* x does not appear in t, SKI convert the term and 
         apply the K combinator *)
      let T := type of t in
        start_ski t ltac:(fun t' => 
        k (@SKI.K T X t'))

 ) || (

   (* t has at least one occurence of x *)
   match t with 

   (* application case *)
   | ?f ?g =>
     let T := type of f in
     match eval hnf in T  with
     | ?A -> ?B =>
        ( check_not_contains x f;
            (* only g has occurences of x *)
            start_ski f ltac:(fun f' =>
            do_ski x g  ltac:(fun g' => 
            k (@SKI.B X A B f' g')))

        ) || (
          check_not_contains x g;
            (* only f has occureces of x *)
            do_ski x f  ltac:(fun f' =>
            start_ski g ltac:(fun g' => 
            k (@SKI.C X A B f' g')))

        ) || ( 
            (* f and g both have occurences of x *)
            do_ski x f ltac:(fun f' =>
            do_ski x g ltac:(fun g' => 
            k (@SKI.S X A B f' g')))
        ); fail 5
     end

   (* lambda case *)
   | (fun somevar:_ => _) =>
     let T := type of t in 
     match eval hnf in T with
     | ?A -> ?B => (* only work on non-dependent functions *)

      (* Generate a new evar.  This will hold the result
         when we compute it. *)
      let output := fresh "output" in
      evar (output:X -> A -> B);

      (* Assert a dumb sub-goal. This gets us get a fresh
         variable of type A in the context; we can apply this
         to t, eliminating the lambda by beta-reduction.
       *)
      let H := fresh "H" in
      assert (H:A -> A);
        [ try (
          (* get a fresh variable of type A in the context *)
          let a := fresh "a" in
          intro a;

          (* apply a to t and reduce the resulting beta redex *)
          let t' := eval cbv beta in (t a) in

          (* t' is now the body of t with the bound variable
             replaced by a.  First SKI convert with respect to
             a, then SKI convert _again_ with respect to x;
             then simplify.
           *)
          do_ski a t' ltac:(fun m =>
          do_ski x m  ltac:(fun m' =>
          ski_simpl_loop m' ltac:(fun m'' =>

            (* Now we force the 'output' evar to unify with
               the SKI converted term. This makes the term
               we calculated avaliable in the other subgoal.
             *)
            let out_evar := eval unfold output in output in
            unify m'' out_evar;
            
            (* finally, we finish the sub goal *)
            exact a
          ))))
          ; fail 5 (* if something goes wrong, propigate failure upward *)
        | 
          (* The evar is instantiated via the funky stuff we did
             in the assert subgoal.  Now we extract the answer,
             clean up after ourselves, and enter the continuation.
          *)
          let m := eval unfold output in output in
          clear H output;
          k m
        ]

     | _ => fail 5 "cannot SKI convert dependent functions"
     end

   (* case for variable x *)  
   | x => k (@I X)

   | _ => 
     (* This doesn't seem to work as intended?
        I'm not sure why. *)

     (* final case: x must appear somewhere inside something we don't know
        how to convert: e.g., inside a "fix" construct.  Use "pattern"
        reabstract over x and return the resulting lambda term.
      *)
        match eval pattern x in t with
        | ?ft _ => k ft
        end;
        fail 5 "it didn't work"
   end
 )

(* SKI convert 't'. 
   Return the answer into continuation 'k'. *)

with start_ski t k :=
  match t with

  (* Application case.  Just convert each term and compose together *)
  | ?f ?g => 
      start_ski f ltac:(fun f' =>
      start_ski g ltac:(fun g' =>
         k (f' g')))

  (* Lambda case. Similar to lambda case for 'do_ski', but a little simpler.
     Note the double recursion is missing here.
   *)
  | (fun somevar:_ => _) =>
    let T := type of t in
    match eval hnf in T with
    | ?A -> ?B => (* only work on non-dependent functions *)

      let output := fresh "output" in
      evar (output:A -> B);

      let H := fresh "H" in
      assert (H:A -> A);
        [ try (
          let a := fresh "a" in
          intro a;

          let t' := eval cbv beta in (t a) in
       
          do_ski a t' ltac:(fun m =>
          ski_simpl_loop m ltac:(fun m' =>

            let out_evar := eval unfold output in output in
            unify m' out_evar;
            exact a
          ))); 
          fail 4 (* if something goes wrong, propigate failure upward *)
        | 
          let m := eval unfold output in output in
          clear H output;
          k m
        ]

    | _ => fail 4 "cannot SKI convert dependent functions"
    end

  (* We hit something not a lambda and not an application.
     Return it unchanged.
   *)
  | _ => k t
  end.


(* perform SKI simplification in the goal *)
Ltac ski_simpl_goal :=
  match goal with [ |- ?G ] =>
    ski_simpl_loop G ltac:(fun G' => change G')
  end.

(* perform SKI simplification in a hypothesis *)
Ltac ski_simpl_hyp H :=
  let X := type of H in
    ski_simpl_loop X ltac:(fun X' => change X' in H).

(* convert term 't' in the goal *)
Ltac ski_in_goal t :=
   start_ski t       ltac:(fun t' =>
   ski_simpl_loop t' ltac:(fun t'' =>
     change t with t'')).

(* convert term 't' in hypothesis 'H' *)
Ltac ski_in_hyp t H :=
   start_ski t       ltac:(fun t' => 
   ski_simpl_loop t' ltac:(fun t'' =>
     change t with t'' in H)).

(* convert the entire goal *)
Ltac ski_goal :=
   match goal with [ |- ?G ] => 
      start_ski G       ltac:(fun G' =>
      ski_simpl_loop G' ltac:(fun G'' =>
       change G''))
   end.

(* convert an entire hypothesis *)
Ltac ski_hyp H :=
   let X := type of H in   
     start_ski X       ltac:(fun X' =>
     ski_simpl_loop X' ltac:(fun X'' =>
       change X'' in H)).

(* Tactics to unfolding all the combinators, getting
   back lambda expressions.
 *)
Hint Unfold S K I B C : ski_unfold.
Ltac unski_goal := autounfold with ski_unfold.
Ltac unski_hyp H := autounfold with ski_unfold in H.

End SKI.

Tactic Notation "ski" constr(t) := (SKI.ski_in_goal t).
Tactic Notation "ski" constr(t) "in" hyp(H) := (SKI.ski_in_hyp t H).

Tactic Notation "ski" := SKI.ski_goal.
Tactic Notation "ski" "in" hyp(H) := (SKI.ski_hyp H).

Tactic Notation "ski_simpl" := (SKI.ski_simpl_goal).
Tactic Notation "ski_simpl" "in" hyp(H) := (SKI.ski_simpl_hyp H).

Tactic Notation "unski" := (SKI.unski_goal).
Tactic Notation "unski" "in" hyp(H) := (SKI.unski_hyp H).

Notation "`S" := SKI.S (at level 0) : ski_scope.
Notation "`K" := SKI.K (at level 0) : ski_scope.
Notation "`I" := SKI.I (at level 0) : ski_scope.
Notation "`B" := SKI.B (at level 0) : ski_scope.
Notation "`C" := SKI.C (at level 0) : ski_scope.
