From Stdlib Require Import Unicode.Utf8.
From Stdlib Require Import Lia.
From Stdlib Require Import String.
From Stdlib Require Import List.

Open Scope string_scope.

(*

-----------READ ME----------------
 1) Utilizzare il blocco di importazione sottostante se si utilizza una versione 
    di Rocq precedente alla 9.0.1.
 2) Nel file sono presenti numerose sezioni di codice commentate, rappresentano 
    metodi alternativi di risoluzione delle dimostrazioni, a volte più verbosi 
    altre più coincisi.
 3) Si faccia riferimento alla documentazione per una descrizione più dettagliata
*)

(*
Require Import List.
Require Import Lia.
Require Import String.
Require Import Unicode.Utf8.
Import String.
Import Lia.

Open Scope string_scope.
*)


Inductive T: Type := 
| Bool : T
| arrow_type : T -> T -> T.

Notation "A '-->' B" := (arrow_type A B) (at level 99, right associativity).



Inductive t: Type := 
| var : string -> t
| fun_t : string -> T -> t -> t
| app : t -> t -> t
| true : t
| false : t
| if_t : t -> t -> t -> t.

Notation "'App' '(' term1 ',' term2 ')'" := (app term1 term2) (at level 40).
Notation "'Fun' '(' var ':=' type ')' '{' term '}'" := (fun_t var type term) (at level 40).
Notation "'If' '(' term1 ')' '{' term2 'otherwise' term3 '}'" := (if_t term1 term2 term3) (at level 40).



Fixpoint subst (x : string) (s : t) (term : t) {struct term}: t :=
match term with
| var y => if String.eqb x y then s else var y
| Fun(y := type) {term} => if String.eqb x y then Fun(y := type) {term} else Fun(y := type) {subst x s term}
| App(term1, term2) => App((subst x s term1), (subst x s term2))
| true => true
| false => false
| If(term1) {term2 otherwise term3} => If(subst x s term1) {(subst x s term2) otherwise (subst x s term3)}
end.

Notation "e '[' x '/' s ']' " := (subst x s e) (at level 9, x at level 0, s at level 9).




Inductive val : t -> Prop :=
| true_v  : val true
| false_v : val false
| fun_v   : forall (var : string) (type : T) (term : t), val ( Fun(var := type) {term} ).

Notation "v 'is' 'a' 'value'" := (val v) (at level 40).
(*
questa notazione non significa "v ha tipo value", bensi, "v è un valore"
*)




Reserved Notation "t1 '=>>' t2" (at level 40).

Inductive single_step : t -> t -> Prop :=
| beta_s : forall x type e v2, v2 is a value -> App((Fun(x := type) {e}), v2) =>> e[x/v2]
| app1_s : forall a1 a1' a2, a1 =>> a1' -> App(a1, a2) =>> App(a1', a2)
| app2_s : forall v1 a2 a2', v1 is a value -> a2 =>> a2' -> App(v1, a2) =>> App(v1, a2')
| ift_s : forall t1 t2, If(true) {t1 otherwise t2} =>> t1
| iff_s : forall t1 t2, If(false) {t1 otherwise t2} =>> t2
| if_s : forall t1 t1' t2 t3, t1 =>> t1' -> If(t1) {t2 otherwise t3} =>> If(t1') {t2 otherwise t3}

where "t1 '=>>' t2" := (single_step t1 t2).




Inductive multi_step : t -> t -> Prop :=
| ms_refl : forall t, multi_step t t
| ms_step : forall t1 t2 t3, t1 =>> t2 -> multi_step t2 t3 -> multi_step t1 t3.

Notation "t1 '=>>*' t2" := (multi_step t1 t2) (at level 40).



(*
La sezione riguardante la notazione delle liste e presa dalla documentazine di Rocq prover 
Library Stdlib.Lists.List
*)

Open Scope list_scope.

Module ListNotations.
Notation "[ ]" := nil (format "[ ]") : list_scope.
Notation "[ x ]" := (cons x nil) : list_scope.
Notation "[ x ; y ; .. ; z ]" := (cons x (cons y .. (cons z nil) ..))
  (format "[ '[' x ; '/' y ; '/' .. ; '/' z ']' ]") : list_scope.
End ListNotations.

Import ListNotations.


Definition env := list (string * T).

Fixpoint find_type (x: string) (gamma: env) {struct gamma}: option T :=
match gamma with
| [] => None
| (y, type) :: l => if String.eqb y x then Some type else find_type x l
end.

Notation "'Find' x 'within' '{' gamma '}'" := (find_type x gamma) (at level 40).



Inductive type_sys : env -> t -> T -> Prop :=
| base_r : forall gamma x type,
  Find x within {gamma} = Some type ->
  type_sys gamma (var x) type
| app_r : forall gamma t1 t2 type1 type2,
  type_sys gamma t1 (type2 --> type1) ->
  type_sys gamma t2 type2 ->
  type_sys gamma (App(t1, t2)) type1
| lambda_r : forall gamma x t1 type1 type2,
  type_sys ((x, type2) :: gamma) t1 type1 ->
  type_sys gamma (Fun(x := type2) {t1}) (type2 --> type1)
| true_r : forall gamma,
  type_sys gamma true Bool
| false_r : forall gamma,
  type_sys gamma false Bool
| if_r : forall gamma t1 t2 t3 type1,
  type_sys gamma t1 Bool ->
  type_sys gamma t2 type1 ->
  type_sys gamma t3 type1 ->
  type_sys gamma (If(t1) {t2 otherwise t3}) type1.

Notation "gamma '|-' e ':::' type" := (type_sys gamma e type) (at level 40).



(*
=====================================================================================


¬(∃ S T, ⊢λx:S, x x : T).

*)

Fixpoint size (type : T) : nat :=
match type with
| Bool => 1
| type1 --> type2 => 1 + size type1 + size type2
end.

Theorem theo1 : ~ (exists S T, 
[] |- Fun("x" := S) {App(var "x", var "x")} ::: T).
Proof.
unfold not.
intros [S [T H]].
inversion H. subst. clear H.
inversion H5. subst. clear H5.
inversion H2. subst. clear H2.
inversion H4. subst. clear H4.
simpl in *.

injection H1 as H_eq.
injection H2 as H.
rewrite H in H_eq. clear H.
apply (f_equal size) in H_eq.
simpl in H_eq.
lia.
Qed.


(*

⊢ λx:Bool→Bool, λy:Bool→Bool, λz:Bool, y (x z) : T.
assumo che il tip B fosse un errore

*)

Theorem theo2 : exists T, [] |- 
Fun("x" := Bool --> Bool) {
Fun("y" := Bool --> Bool) {
Fun("z" := Bool) {
App(var "y", App(var "x", var "z"))}}} ::: T.
Proof.
exists ((Bool --> Bool) --> ((Bool --> Bool) --> (Bool --> Bool))).
apply lambda_r.
apply lambda_r.
apply lambda_r.
eapply app_r.
- apply base_r.
simpl.
reflexivity.
- eapply app_r.
+ apply base_r.
simpl.
reflexivity.
+ apply base_r.
simpl.
reflexivity.
Qed.

(*
exists ((Bool --> Bool) --> ((Bool --> Bool) --> (Bool --> Bool))).
repeat econstructor.
*)


(*

(λx:Bool → Bool, x) ((λx:Bool, if x then false else true) true) =>>* false

*)

Proposition prop1 :
App ( Fun("x" := Bool --> Bool) {var "x"}, 
App ( Fun("x" := Bool) {If(var "x") {false otherwise true}}, true)
) =>>* false.
Proof.
eapply ms_step.
- apply app2_s; econstructor.
apply true_v.
- simpl .
eapply ms_step.
+ apply app2_s; econstructor.
+ eapply ms_step.
* apply beta_s.
apply false_v.
* simpl.
apply ms_refl.
Qed.

(*
eapply ms_step.
- apply app2_s.
+ apply fun_v.
+ apply beta_s.
apply true_v.
-	simpl .
eapply ms_step.
+ apply app2_s.
* apply fun_v.
* apply ift_s.
+ eapply ms_step.
* apply beta_s.
apply false_v.
* simpl.
apply ms_refl.
*)

(*

Subject Reduction:
∀ t t' T, ( ⊢ t : T ∧ t ➾ t' ) ⟹ ⊢ t' : T.

*)


Lemma sub_context : forall gamma1 gamma2 e T,
gamma1 |- e ::: T ->
(forall (y : string) type, Find y within {gamma1} = Some type -> Find y within {gamma2} = Some type) ->
gamma2 |- e ::: T.
Proof.
intros gamma1 gamma2 e T H. generalize dependent gamma2.
induction H; intros gamma2 Hsub; econstructor; eauto.
apply IHtype_sys. intros y type' H_eq. simpl in *. destruct (String .eqb_spec x y); eauto.
Qed.

(*
intros gamma1 gamma2 e T H. generalize dependent gamma2.
induction H; intros gamma2 Hsub.
- apply base_r. apply Hsub. exact H.
- eapply app_r; eauto.
- apply lambda_r. apply IHtype_sys.
intros y type' H_eq. simpl in *. destruct (String.eqb_spec x y).
+ exact H_eq.
+ apply Hsub in H_eq. rewrite H_eq. reflexivity.
- apply true_r.
- apply false_r.
- eapply if_r; eauto.
*)


Lemma empty_context: forall gamma v U,
[] |- v ::: U ->
gamma |- v ::: U.
Proof.
intros gamma v U H.
eapply sub_context. eauto.
intros y type H_search. simpl in H_search. discriminate H_search.
Qed.



Lemma substitution_preserves_type : forall e gamma x U v T,
((x, U) :: gamma) |- e ::: T ->
[] |- v ::: U ->
gamma |- e [x / v] ::: T.
Proof.
induction e; intros gamma x U v T He Hv; simpl in *;
inversion He; subst; clear He;
try solve [econstructor; eauto].
- destruct (String.eqb_spec x s).
  + subst s. simpl in H1. destruct (String.eqb_spec x x); [|contradiction].
    injection H1 as H. apply empty_context. subst. exact Hv.
  + simpl in H1. destruct (String.eqb_spec x s); [contradiction | apply base_r; exact H1].   
- destruct (String.eqb_spec x s).
  + subst s. apply lambda_r. eapply sub_context; eauto.
    intros y type' H_search. simpl in *. destruct (String.eqb_spec x y); eauto.
  + apply lambda_r. eapply IHe; eauto.
    eapply sub_context; eauto.
    intros y. simpl. destruct (String.eqb_spec s y).
    * subst y. destruct (String.eqb_spec x s); [contradiction | eauto].
    * destruct (String.eqb_spec x y); [eauto | eauto].
Qed.


(*
intro e.
induction e; intros gamma x U v T He Hv; simpl.
- inversion He; subst. destruct (String.eqb_spec x s).

+ subst s. simpl in H1. destruct (String.eqb_spec x x).
* injection H1 as H1; subst. apply empty_context. exact Hv.
* contradiction.
+ simpl in H1. destruct (String.eqb_spec x s).
* contradiction.
* apply base_r. exact H1.

- inversion He; subst. destruct (String.eqb_spec x s).
+ subst s. apply lambda_r. eapply sub_context.
* exact H4.
* intros y type' H_search. simpl in *. destruct (String.eqb_spec x y).
-- exact H_search.
-- exact H_search.
+ apply lambda_r. eapply IHe.
* eapply sub_context; eauto.
intros y. simpl. destruct (String.eqb_spec s y).
    ** subst y. destruct (String.eqb_spec x s); [contradiction | eauto].
    ** destruct (String.eqb_spec x y); eauto.
* exact Hv.

- inversion He; subst. eapply app_r.
+ eapply IHe1; eauto.
+ eapply IHe2; eauto.

- inversion He; subst. apply true_r.

- inversion He; subst. apply false_r.

- inversion He; subst. eapply if_r.
+ eapply IHe1; eauto.
+ eapply IHe2; eauto.
+ eapply IHe3; eauto.
*)


Theorem theo3 : forall t t' T, 
([] |- t ::: T) /\ (t =>>* t') -> 
[] |- t' ::: T.
Proof.
intros t0 t' T0 [Htype Hstep].
induction Hstep.
- exact Htype.
- apply IHHstep; clear IHHstep; clear Hstep.
generalize dependent T0.
induction H; intros T0 Htype.
+ inversion Htype. subst.
inversion H3. subst.
eapply substitution_preserves_type; eauto.
+ inversion Htype; subst.
eapply app_r; eauto.
+ inversion Htype; subst.
eapply app_r; eauto.
+ inversion Htype; subst. exact H5.
+ inversion Htype; subst. exact H6.
+ inversion Htype; subst.
eapply if_r; auto.
Qed.
