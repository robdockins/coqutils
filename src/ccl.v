(* Robert Dockins (c) 2013.
   
   Tactics for Categorical Combinatory Logic (CCL).
 
   These tactics will transform Gallina terms into
   "points-free" form using Curien's categorical combinators.
   
   The transformation is essentially the same transformation
   that is used to interpret lambda-calculi in a cartesian
   closed category; hence the name.  Algorithmically, the
   transformation is quite similar to the translation for
   sending named lambda terms to de Brujin representation.


   See the following for a formal exposition of CCL:

   P.-L. Curien "Categorical Combinators",
     in _Information and Control_, no. 69,
     pages 188--254, 1986.


   Note: the tactics cannot handle some things, like
     dependent functions or variables appearing
     in pattern matches or inside explicit fixpoints.
     Don't expect too much.
 *)

Delimit Scope ccl_scope with ccl.
Open Scope ccl_scope.

Reserved Notation "f ∘ g" 
  (at level 40, left associativity,
  format
    "'[hv' f  '∘' '/'  g ']'"
  ).
Reserved Notation "〈 f , g 〉" 
  (format
    "'[hv' '〈' f '/' ','  g '/' '〉' ']'"
  ).
Reserved Notation "'Λ' f" 
  (f at next level, at level 0,
  format
    "'[hv' 'Λ' f ']'"
  ).

Notation π₁ := (@fst _ _).
Notation π₂ := (@snd _ _).

Module CCL.

(* The basic combinators of CCL *)
Definition Id A (a:A) : A := a.
Definition compose A B C (f:B -> C) (g:A -> B) x := f (g x).
Definition curry A B C (f:A*B->C) (x:A) (y:B) : C := f (x,y).
Definition app A B (x:(A -> B) * A) : B := fst x (snd x).
Definition pairing A B C (f:A->B) (g:A->C) (x:A) : B*C := (f x, g x).

Arguments Id {A} a.
Arguments compose {A} {B} {C} f g x.
Arguments curry {A} {B} {C} f x y.
Arguments app {A} {B} x.
Arguments pairing {A} {B} {C} f g x.

Notation "f ∘ g"  := (@compose _ _ _ f g).
Notation "〈 f , g 〉" := (@pairing _ _ _ f g).
Notation "'Λ' f" := (@curry _ _ _ f).
Notation K' A B := (curry (@fst A B)) (only parsing).
Notation K := (curry (@fst _ _)).

(* Extra combinators for Pi types *)
Definition ALL (A:Type) (P:A -> Prop) : Prop :=
  forall a:A, P a.
Definition ALLT (A:Type) (P:A -> Type) : Type :=
  forall a:A, P a.

(* I explicitly introduce a combinator for variables rather than
   using the raw projections.  This leads to shorter-appearing
   conversions; however, I'm not 100% convinced this is worthwhile...
 *)
Fixpoint prods (A:Type) (XS:list Type) : Type :=
  match XS with
  | nil => A
  | cons X XS' => prod (prods A XS') X
  end.

Fixpoint var_proj (X:Type) (Y:Type) (G:list Type) : prods (X*Y) G -> Y :=
  match G as G' return prods (X*Y) G' -> Y with
  | nil => @snd X Y
  | cons G1 GS => var_proj X Y GS ∘ @fst (prods (X*Y) GS) G1 
  end.

(* The nat isn't needed to implement the stack of projections, and is
   completely ignored here. It's only here so that later, when I use
   notation to hide X Y and G, the user looking at converted terms
   can tell the different variables apart by their de Brujin numbers.
 *)
Definition var X Y G (n:nat) := var_proj X Y G.

(* Here we show that Coq's conversion system satisfies most of
   the rules of Curien's CCL.
 *)
Lemma Assoc A B C D (x:C -> D) (y:B -> C) (z:A -> B) :
  (x ∘ y) ∘ z = x ∘ (y ∘ z).
Proof refl_equal.

Lemma IdL A B (x:A->B) :
  Id ∘ x = x.
Proof refl_equal.

Lemma IdR A B (x:A->B) :
  x ∘ Id  = x.
Proof refl_equal.

Lemma Fst A B C (x:A->B) (y:A->C) :
  π₁ ∘ 〈 x, y 〉 = x.
Proof refl_equal.

Lemma Snd A B C (x:A->B) (y:A->C) :
  π₂ ∘ 〈 x, y 〉 = y.
Proof refl_equal.

Lemma Dpair A B C D (x:A -> B) (y:A -> C) (z:D -> A) :
  〈 x, y 〉 ∘ z = 〈 x ∘ z, y ∘ z 〉.
Proof refl_equal.

Lemma Beta A B C (x:A*B ->C) (y:A->B) :
  app ∘ 〈 Λ x, y 〉 = x ∘ 〈 Id, y 〉.
Proof refl_equal.

Lemma Dlam A B C X (x:A*B ->C) (y:X ->A) :
  Λ x ∘ y = Λ (x ∘ 〈 y ∘ π₁, π₂ 〉). 
Proof refl_equal.

Lemma AI A B : Λ (@app A B) = (@Id (A->B)).
Proof refl_equal.

Remark FSI A B : 
  〈 π₁, π₂ 〉 = @Id (A*B).
Abort. 
(* can't prove by conversion; needs functional extensionality
   and case analysis of pairs *)

Lemma FSA A B :
  app ∘ 〈 π₁, π₂ 〉 = @app A B.
Proof refl_equal.

Lemma ass A B C (x:B->C) (y:A->B) (z:A) :
  (x ∘ y) z = x (y z).
Proof refl_equal.

Lemma fst' A B (x:A) (y:B) :
  π₁ (x,y) = x.
Proof refl_equal.

Lemma snd' A B (x:A) (y:B) :
  π₂ (x,y) = y.
Proof refl_equal.
 
Lemma dpair X A B (x:X ->A) (y:X -> B) (z:X) :
  〈 x, y 〉 z = (x z, y z).
Proof refl_equal.

Lemma app' A B (x:A->B) (y:A) :
  app (x,y) = x y.
Proof refl_equal.

Lemma beta A B C (x:A*B->C) (y:A) (z:B) :
  Λ(x) y z = x (y,z).
Proof refl_equal.

Lemma Quote1 A B C (x:A) (y:B->C) :
  K x ∘ y = K x.
Proof refl_equal.

Lemma Quote2 A B C X (x:X -> B -> C) (y:X) (z:A->B) :
  app ∘ 〈 x ∘ K y, z 〉 = x y ∘ z.
Proof refl_equal.

Lemma Quote2a A B C (x:B -> C) :
  K' _ A x = Λ (x ∘ π₂).
Proof refl_equal.
 
Lemma Quote2b A B C (x:B -> C) (y:B) :
  K' _ A (x y) = x ∘ K y. 
Proof refl_equal.

Lemma Beta' X A B C (x:A*B -> C) (y:X->A) (z:X->B) :
  app ∘ 〈 Λ(x) ∘ y, z 〉 = x ∘ 〈 y, z 〉.
Proof refl_equal.

(* The above lemmas show that Coq satisfies the laws
   of CCLβηP at the level of conversion.

   However, FSI is not satisfied, so we do not get CCLβηSP.
 *)

(* This rewrite is a useful consequence of the above.
   It also follows directly via conversion.
 *)
Lemma appK A B C (x:B ->C) (y:A ->B) :
  app ∘ 〈K x, y〉 = x ∘ y.
Proof refl_equal.


(* We can set up these rules into rewrite systems.
   However, autorewrite is pretty slow -- and besides, all
   these identities hold up to conversion, so using rewrites
   feels a little silly...
 *)
Hint Rewrite Assoc IdL IdR Fst Snd Dpair Beta Beta' Dlam appK : ccl_simpl.
Hint Rewrite AI FSA Quote1 Quote2 : ccl_simpl.
Hint Rewrite ass fst' snd' dpair app' beta : ccl_exec.


(* do_ccl_simpl t k

   Examine the term t, looking for a variety of simplifications.
   These include redex rules for each combinator and a variety
   of different eta contractions and other identities.
 
   If a redex is found, enter continuation 'k' with the reduced term.

   Why define this thing?  It's _way_ faster than autorewrite and using
   it to drive a "change" tactic means you don't produce any proof
   structure; hence Qed is also faster.
 *)
Ltac do_ccl_simpl t k :=
   match t with

    | appcontext G [ (app ∘ pairing (K' (?A -> ?B) ?X ?f) (K' _ _ ?g)) ] =>
        let G' := context G [(K' B X (f g))] in k G'

    | appcontext G [ (app ∘ 〈 K ?x, ?y 〉) ?z ] =>
        let G' := context G [ x (y z) ] in k G' 

    | appcontext G [ (app ∘ 〈 K ?x, ?y 〉) ] =>
        let G' := context G [ x ∘ y ] in k G' 

    | appcontext G [ ((?x ∘ ?y) ∘ ?z) ] =>
        let G' := context G [ x ∘ (y ∘ z) ] in k G' 

    | appcontext G [ @fst _ _ ∘ 〈 ?x, _ 〉 ] =>
        let G' := context G [ x ] in k G'

    | appcontext G [ @snd _ _ ∘ 〈 _ , ?y 〉 ] =>
        let G' := context G [ y ] in k G'

    | appcontext G [ 〈 ?x, ?y 〉 ∘ ?z ] =>
        let G' := context G [ 〈 x ∘ z , y ∘ z 〉 ] in k G'

    | appcontext G [ app ∘ 〈 Λ(?x) , ?y 〉 ] =>
        let G' := context G [ x ∘ 〈 Id, y 〉 ] in k G'

    | appcontext G [ Λ(@app ?A ?B) ] =>
        let G' := context G [ @Id (A->B) ] in k G'

    | appcontext G [ curry ?x ∘ ?y ] =>
        let G' := context G [ Λ( x ∘ 〈 y ∘ π₁ , π₂ 〉) ] in k G'

    | appcontext G [ @app ?A ?B ∘ 〈 π₁, π₂ 〉 ] =>
        let G' := context G [ @app A B ] in k G'

    | appcontext G [ Λ(?x) ?y ?z ] =>
        let G' := context G [ x (y,z) ] in k G'

    | appcontext G [ @fst _ _ ( ?x , _) ] =>
        let G' := context G [ x ] in k G'

    | appcontext G [ @snd _ _ ( _ , ?y) ] =>
        let G' := context G [ y ] in k G'

    | appcontext G [ (?x ∘ ?y) ?z ] =>
        let G' := context G [ x (y z) ] in k G'

    | appcontext G [ 〈 ?x, ?y 〉 ?z ] =>
        let G' := context G [ (x z, y z) ] in k G'

    | appcontext G [ app ( ?x, ?y ) ] =>
        let G' := context G [ x y ] in k G'

    end.

(* Continue applying reduction rules until no more are found.
   Then enter the continuation.
 *)
Ltac ccl_simpl_loop t k :=
  try (do_ccl_simpl t ltac:(fun t' => ccl_simpl_loop t' k)) || k t.

(* do_ccl G find_var t k

   Convert term t into CCL form in variable context G.
     'find_var' is a function that will find variables
     'k' is a continuation expecting the converted term.

   This is the main meat of the CCL conversion tactic, and the
   way it works is pretty tricky.  

   'G' is a type which is built up as a product of the types of
   the "open" variables in term 't'. Ultimately, we will take
   the term 't', of type T and translate it into a function
   of type 'G -> T'.  Variables get converted into a telescope
   of pair projection functions that select out the elements of
   the context (of type G).  Each time we pass under a lambda,
   the type G grows by a new type on the right.

   The 'find_var' function expects three arguments:
     1) the term to examine
     2) a continuation to enter if a variable is found
     3) a continuation to enter if no variable is found

   Initially (starting with a closed term) the find_var function just
   always enters its "no variable found" continuation.  Every time we
   pass under a lambda, we extend the 'find_var' function to look for
   the new variable.  We play continuation passing games so that
   variables end up getting shuffled around the right way.
 
   If the find_var function doesn't detect that 't' is one of the
   variables, it goes into a big match statement that examines the
   structure of 't', performing appropriate translations in each
   case, following the translation given by Curien.  I have extended
   this translation to handle the occurance of Pi types; I'm not
   completely convinced this is very useful, but it is cute.

   There are some very strange goings-on in the case for lambdas
   in order to achieve the effect of opening the term.
 *)

Ltac do_ccl G find_var t k :=
  (* first look for variables *)
  find_var t 

  (* if we find one, package it up using the var combinator and jump to k *)
  ltac:(fun X Y l n => k (@var X Y l n))

  (* if not jump in here and start examining the structure of t *)
  ltac:( 

  idtac; (* This needs to be here to avoid an error about locally-defined
            ltacs not being able to directly go into match constructs.
            Don't ask me why, because I couldn't possibly tell you. *)

  match t with
  | @fst ?A ?B ?x =>
     do_ccl G find_var x ltac:(fun x' =>
       k ((@fst A B) ∘ x'))

  | @snd ?A ?B ?x =>
     do_ccl G find_var x ltac:(fun x' =>
       k ((@snd A B) ∘ x'))

  | (?f, ?g) =>
     do_ccl G find_var f ltac:(fun f' =>
     do_ccl G find_var g ltac:(fun g' =>
       k (pairing f' g')))
   
  (* lambda case *)
  | (fun z:?Z => _ ) =>
     let T := type of t in 
     match eval hnf in T with
     | ?A -> ?B => (* only work on non-dependent functions *)

      (* Our main goal here is to get a new variable of type 'A' into our
         proof context so we can open the body of 't' by applying it.
     
         We do this by asserting the trivial lemma (A -> A).  In the subgoal
         for this lemma, we make temporary use of the fresh 'A' variable
         to drive the conversion.  However, we need the term we calculate
         to be avaliable in the other, main, proof subgoal.  To facilitate
         this communication between subgoals, we introduce a new evar here.

         This evar will be instantiated in the first subgoal and then that
         instantiation will be used in the second subgoal.
       *)
      let output := fresh "output" in
      evar (output:G*A -> B);

      (* Assert a dumb subgoal to facilitate getting a variable of type 'A'
         in the context.
       *)
      let H := fresh "H" in
      assert (H:A -> A);

        [ (* we put everything here in a try block so that if a failure occurs
             we can "fail 1"  instead, which is enough to force the main match
             block we are in to backtrack.
           *)
          try (

          (* (a:A) is now a fresh variable *)
          let a := fresh "a" in intro a;

          (* open the body of 't' by applying a and beta reducing *)
          let t' := eval cbv beta in (t a) in
       
          (* Now we have to update the "search for a variable" continuation
             If we see 'a', return an empty list, indicating that we can
             immediately project the rightmost component of the context (which
             will have type G*A). This is basically de Brujin variable 0.  If
             we do not see 'a', enter the old 'find_var' continuation. However,
             if the old find_var finds a variable, we need to cons a new type
             onto the list, indicating an extra π₁ projection is needed;
             basically we have to increase the de Brujin index by 1.
           *)
          let find_var' := (fun t k krest =>
             match t with
             | a => k G A (@nil Type) O
             | _ => find_var t 
                       ltac:(fun X Y G n => k X Y (@cons Type A G) (S n))
                       krest
             end) in

          (* Now recursively enter the body of t with the extended environment
             type and find_var continaution.
           *)
          do_ccl (G*A)%type find_var' t' ltac:(fun m =>
          ccl_simpl_loop m ltac:(fun m' =>

            (* Now we've calulcated our answer; force the evar we introduced
               above to unify with the new term we calculated.
             *)
            let out_evar := eval unfold output in output in
            unify m' out_evar;

            (* Now we can finish this subgoal *)
            exact a

          ))); fail 1 (* If something goes wrong, propigate failure upward 
                         to force backtracking. *)
        |  
          (* If we get here, the previous subgoal completed and unified
             the output evar with the converted body of t.  Now we retrieve
             that answer, apply the 'curry' combinator and pass the result into 'k'.
           *)
          let m := eval unfold output in output in
          clear H output;
          k (curry m)
        ]
    end

  (* Application case.  Pretty straightforward; just recursively enter each
     side and put together the result using the app and pairing combinators.
   *)
  | ?f ?g => 
     let T := type of f in 
     match eval hnf in T with
     | ?A -> ?B =>

       do_ccl G find_var f ltac:(fun f' =>
       do_ccl G find_var g ltac:(fun g' =>
       k (app ∘ (pairing f' g'))))

     end

    (* This is pretty fancy. Is it good for anything?? 

       Mostly it keeps the whole thing from crashing out if we convert
       terms with Props that have forall or implication in them.
     *)
  | (forall a:?A, @?P a) =>
       let TP := type of P in
       match TP with
       | _ -> Prop =>

         do_ccl G find_var P ltac:(fun P' =>
            k (ALL A ∘ P'))

       | _ -> Type =>

         do_ccl G find_var P ltac:(fun P' =>
            k (ALLT A ∘ P'))

       end


  (* Fallthrough case.  The previous cases failed, so assume 't' is a
     constant of some sort and translate it using the 'K' combinator.

     If t is actually something else (e.g., a primitive fixpoint) that actually
     contains one of the free variables, things will eventually fall apart when
     we later try to to a "change".
   *)
  | _ =>

     let T := type of t in
       k (K' T G t)

  end).

(* start_ccl t k

   CCL translate the term t and pass the result to continuation k.

   This gets things started with an empty context (i.e., type unit)
   and a find_var continuation that immediately jumps to the 'krest'
   continuation.
 *)
Ltac start_ccl t k :=
  let find_var := fun t k krest => krest in
  do_ccl unit find_var t k.
  

(* Testing tactic.  Translate the term t and assert 
   that the translation is equal to the original.
 *)
Ltac ccl_test t :=
  start_ccl t ltac:(fun t' => 
  ccl_simpl_loop (t' tt) ltac:(fun t'' =>
    assert (t = t''))).

(* Perform CCL simplification in the goal *)
Ltac ccl_simpl_goal :=
  match goal with [ |- ?G ] =>
    ccl_simpl_loop G ltac:(fun G' => change G')
  end.

(* perform CCL simplification in a hypothesis *)
Ltac ccl_simpl_hyp H :=
  let X := type of H in
    ccl_simpl_loop X ltac:(fun X' => change X' in H).

(* convert term 't' in the goal *)
Ltac ccl_in_goal t :=
   start_ccl t ltac:(fun t' =>
   ccl_simpl_loop (t' tt) ltac:(fun t'' =>
     change t with t'')).

(* convert term 't' in hypothesis 'H' *)
Ltac ccl_in_hyp t H :=
   start_ccl t ltac:(fun t' => 
   ccl_simpl_loop (t' tt) ltac:(fun t'' =>
     change t with t'' in H)).

(* convert the entire goal *)
Ltac ccl_goal :=
   match goal with [ |- ?G ] => 
      start_ccl G ltac:(fun G' =>
      ccl_simpl_loop (G' tt) ltac:(fun G'' =>
        change G''))
   end.

(* convert an entire hypothesis *)
Ltac ccl_hyp H :=
   let X := type of H in   
     start_ccl X ltac:(fun X' =>
     ccl_simpl_loop (X' tt) ltac:(fun X'' =>
       change X'' in H)).

(* Tactics to unfold all the combinators, getting
   back lambda expressions.
 *)

Hint Unfold curry app compose Id pairing ALL ALLT : ccl_unfold.

Ltac unccl_goal :=
  unfold var; simpl var_proj;
  autounfold with ccl_unfold;
  simpl fst; simpl snd.

Ltac unccl_hyp H :=
  unfold var; simpl var_proj;
  autounfold with ccl_unfold in H;
  simpl fst in H;
  simpl snd in H.

End CCL.

Tactic Notation "ccl" constr(t) := (CCL.ccl_in_goal t).
Tactic Notation "ccl" constr(t) "in" hyp(H) := (CCL.ccl_in_hyp t H).

Tactic Notation "ccl" := CCL.ccl_goal.
Tactic Notation "ccl" "in" hyp(H) := (CCL.ccl_hyp H).

Tactic Notation "ccl_simpl" := (CCL.ccl_simpl_goal).
Tactic Notation "ccl_simpl" "in" hyp(H) := (CCL.ccl_simpl_hyp H).

Tactic Notation "unccl" := (CCL.unccl_goal).
Tactic Notation "unccl" "in" hyp(H) := (CCL.unccl_hyp H).

Notation "f ∘ g"  := (@CCL.compose _ _ _ f g) : ccl_scope.
Notation "〈 f , g 〉" := (@CCL.pairing _ _ _ f g) : ccl_scope.
Notation "'Λ' f" := (@CCL.curry _ _ _ f) : ccl_scope.
Notation Id := (CCL.Id).
Notation app := (CCL.app).
Notation K' A B := (CCL.curry (@fst A B)) (only parsing). 
Notation K := (CCL.curry (@fst _ _)).
Notation var := (CCL.var _ _ _).
