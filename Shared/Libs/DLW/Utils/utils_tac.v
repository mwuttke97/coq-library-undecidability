(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import Arith List Wellfounded.

Set Implicit Arguments.

Definition eqdec X := forall x y : X, { x = y } + { x <> y }.

Definition swap {X Y} (c : X * Y) := let (x,y) := c in (y,x).

Theorem measure_rect X (m : X -> nat) (P : X -> Type) :
      (forall x, (forall y, m y < m x -> P y) -> P x) -> forall x, P x.
Proof. 
  apply well_founded_induction_type, wf_inverse_image, lt_wf.
Qed.

(*workaround to extract function from term - "match goal with" does not seem to do it (?)*)
Lemma induction_on_aux X (f : X -> nat) (P : X -> Type) : (let t := f in forall (x : X), P x) -> (forall (x : X), f x = f x -> P x).
Proof.
intros H x _. apply H.
Qed.

(*works with coq 8.10 via workaround*)
Tactic Notation "induction" "on" hyp(x) "as" ident(IH) "with" "measure" uconstr(f) :=
  let t := fresh in pattern x; cut (f = f);[|reflexivity]; revert x; apply induction_on_aux; intro t; 
  intro x;  pattern x; revert x; apply measure_rect with (m := t); subst t; intros x IH.

(*
(*does not work with coq 8.10 maybe because f refers to a reverted hypothesis and cannot be resolved*)
Tactic Notation "induction" "on" hyp(x) "as" ident(IH) "with" "measure" uconstr(f) :=
  pattern x; revert x; apply measure_rect with (m := fun x => f); intros x IH.
*)
Tactic Notation "eq" "goal" hyp(H) := 
  match goal with 
    |- ?b => match type of H with ?t => replace b with t; auto end 
  end.

Ltac eqgoal := let H := fresh in intro H; eq goal H; clear H.

Tactic Notation "spec" "in" hyp(H) :=
  let Q := fresh 
  in match goal with G: ?h -> _ |- _ => 
       match G with 
         | H => assert (h) as Q; [ | specialize (H Q); clear Q ] 
       end 
     end.

Ltac solve_list_eq := simpl; repeat progress (try rewrite app_ass; try rewrite <- app_nil_end; simpl; auto); auto.

Tactic Notation "solve" "list" "eq" := solve_list_eq.

Tactic Notation "solve_list_eq" "in" hyp(H) := generalize H; clear H; solve_list_eq; intro H.
(* Tactic Notation "solve" "list" "eq" "in" hyp(H) := generalize H; clear H; solve_list_eq; intro H. *)

Tactic Notation "solve" "list" "eq" "in" hyp(H) := 
   let Q := fresh in 
   match goal with 
     |- ?t => set (Q := t); generalize H; clear H; solve_list_eq; intro H; unfold Q; clear Q
   end.

Ltac msplit n := 
  match n with 
    | 0    => idtac 
    | S ?n => split; [ | msplit n ]
   end.

(*workaround, works with coq 8.10*)
Lemma induction_on_aux2 X Y (f : X -> Y -> nat) (P : X -> Y -> Type) : 
        (let t := f in forall (x : X) (y : Y), P x y) 
     -> (forall (x : X) (y : Y), f x y = f x y -> P x y).
Proof.
intros H x y _. apply H.
Qed.

(*workaround, works with coq 8.10*)
Tactic Notation "define" ident(f) "of" hyp(n) hyp(m) "as" uconstr(t)  :=
  pattern n,m; cut (t = t);[|reflexivity]; revert n m; apply induction_on_aux2; intros f n m.

(*
(*does not work with coq 8.10 - maybe because t referts to hypotheses n m which are distinct from the arguments (n:N) (m:M)*)
Tactic Notation "define" ident(f) "of" hyp(n) hyp(m) "as" uconstr(t)  :=
  match type of n with ?N =>  
    match type of m with ?M  => pose (f (n:N) (m:M) := t) end end.
*)

(* used in induction on with two parameters workaround *)
(* DLW: this one extracts better *)

Section measure_rect2.

  Variable (X Y : Type) (m : X -> Y -> nat) (P : X -> Y -> Type).

  Hypothesis F : (forall x y, (forall x' y', m x' y' < m x y -> P x' y') -> P x y).

  Let m' (c : X * Y) := match c with (x,y) => m x y end.

  Let R c d := m' c < m' d.

  Definition measure_rect2 x y : P x y.
  Proof.
    cut (Acc R (x,y)).
    + revert x y.
      refine (fix loop x y H := @F x y (fun x' y' H' => loop x' y' _)).
      apply (Acc_inv H), H'.
    + apply wf_inverse_image with (f := m'), lt_wf.
  Defined.

End measure_rect2.

Section measure_rect3.

  Variable (X Y Z : Type) (m : X -> Y -> Z -> nat) (P : X -> Y -> Z -> Type).

  Hypothesis F : (forall x y z, (forall x' y' z', m x' y' z' < m x y z -> P x' y' z') -> P x y z).

  Let m' (c : X * Y * Z) := match c with (x,y,z) => m x y z end.

  Let R c d := m' c < m' d.

  Definition measure_rect3 x y z : P x y z.
  Proof.
    cut (Acc R (x,y,z)).
    + revert x y z.
      refine (fix loop x y z H := @F x y z (fun x' y' z' H' => loop x' y' z' _)).
      apply (Acc_inv H), H'.
    + apply wf_inverse_image with (f := m'), lt_wf.
  Defined.

End measure_rect3.

Check measure_rect3.

(*coq 8.10 workaround*)
Tactic Notation "induction" "on" hyp(x) hyp(y) "as" ident(IH) "with" "measure" uconstr(f) :=
  let measure := fresh in define measure of x y as (f : nat); pattern x, y; revert x y; 
  apply measure_rect2 with (m := measure); subst measure; intros x y IH.

(*
does not work with coq 8.10
Tactic Notation "induction" "on" hyp(x) hyp(y) "as" ident(IH) "with" "measure" uconstr(f) :=
  generalize I; intro IH;
  let mes := fresh "measure" in let rel := fresh "relation" in let loop := fresh "loop" in
  let u := fresh "u" in let u' := fresh x in let Hu := fresh "Hu" in 
  let v := fresh "v" in let v' := fresh y in let Hv := fresh "Hv" 
  in clear IH; 
     define mes of x y as (f : nat);
     set (rel u v := mes (fst u) (snd u) < mes (fst v) (snd v)); unfold fst, snd in rel;
     pattern x, y; match goal with
       |- ?T _ _ => 
       refine ((fix loop u v (Hu : Acc rel (u,v)) { struct Hu } : T u v := _) x y _);
       [ assert (forall u' v', rel (u',v') (u,v) -> T u' v') as IH;
         [ intros u' v' Hv; apply (loop u' v'), (Acc_inv Hu), Hv 
         | unfold rel, mes in *; clear mes rel Hu loop x y; rename u into x; rename v into y ]
       | unfold rel; apply wf_inverse_image, lt_wf ]
     end.
*)

Section forall_equiv.

  Variable (X : Type) (A P Q : X -> Prop) (HPQ : forall n, A n -> P n <-> Q n).

  Theorem forall_bound_equiv : (forall n, A n -> P n) <-> (forall n, A n -> Q n).
  Proof.
    split; intros H n Hn; generalize (H _ Hn); apply HPQ; auto.
  Qed.

End forall_equiv.

Section exists_equiv.

  Variable (X : Type) (P Q : X -> Prop) (HPQ : forall n, P n <-> Q n).

  Theorem exists_equiv : (exists n, P n) <-> (exists n, Q n).
  Proof.
    split; intros (n & Hn); exists n; revert Hn; apply HPQ; auto.
  Qed.

End exists_equiv.

