(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

Require Export CRelationClasses.
Require Import Bool CMorphisms.
(* Setoid.*)

Set Implicit Arguments.
Unset Strict Implicit.

(** Structure with nothing inside.
    Used to force a module type T into a module via Nop <+ T. (HACK!) *)

Module Type Nop.
End Nop.

(** * Structure with just a base type [t] *)

Module Type Typ.
  Parameter Inline(10) t : Type.
End Typ.

(** * Structure with an equality relation [eq] *)

Module Type HasEq (Import T:Typ).
  Parameter Inline(30) eq : t -> t -> Type.
End HasEq.

Module Type Eq := Typ <+ HasEq.

Module Type EqNotation (Import E:Eq).
  Infix "==" := eq (at level 70, no associativity).
  Notation "x ~= y" := (eq x y -> False) (at level 70, no associativity).
End EqNotation.

Module Type Eq' := Eq <+ EqNotation.

(** * Specification of the equality via the [Equivalence] type class *)

Module Type IsEq (Import E:Eq).
  Declare Instance eq_equiv : Equivalence eq.
End IsEq.

(** * Earlier specification of equality by three separate lemmas. *)

Module Type IsEqOrig (Import E:Eq').
  Axiom eq_refl : forall x : t, x==x.
  Axiom eq_sym : forall x y : t, x==y -> y==x.
  Axiom eq_trans : forall x y z : t, x==y -> y==z -> x==z.
  Hint Immediate eq_sym : core.
  Hint Resolve eq_refl eq_trans : core.
End IsEqOrig.

(** * Types with decidable equality *)

Module Type HasEqDec (Import E:Eq').
  Parameter eq_dec : forall x y : t, sum (x==y) (x==y -> False).
End HasEqDec.

(** * Boolean Equality *)

(** Having [eq_dec] is the same as having a boolean equality plus
    a correctness proof. *)

Module Type HasEqb (Import T:Typ).
  Parameter Inline eqb : t -> t -> bool.
End HasEqb.

Module Type EqbSpec (T:Typ)(X:HasEq T)(Y:HasEqb T).
  Parameter eqb_eq : forall x y, Y.eqb x y = true -> X.eq x y.
  Parameter eq_eqb : forall x y, X.eq x y -> Y.eqb x y = true.
End EqbSpec.

Module Type EqbNotation (T:Typ)(E:HasEqb T).
  Infix "=?" := E.eqb (at level 70, no associativity).
End EqbNotation.

Module Type HasEqBool (E:Eq) := HasEqb E <+ EqbSpec E E.

(** From these basic blocks, we can build many combinations
    of static standalone module types. *)

Module Type EqualityType := Eq <+ IsEq.

Module Type EqualityTypeOrig := Eq <+ IsEqOrig.

Module Type EqualityTypeBoth <: EqualityType <: EqualityTypeOrig
 := Eq <+ IsEq <+ IsEqOrig.

Module Type DecidableType <: EqualityType
 := Eq <+ IsEq <+ HasEqDec.

Module Type DecidableTypeOrig <: EqualityTypeOrig
 := Eq <+ IsEqOrig <+ HasEqDec.

Module Type DecidableTypeBoth <: DecidableType <: DecidableTypeOrig
 := EqualityTypeBoth <+ HasEqDec.

Module Type BooleanEqualityType <: EqualityType
 := Eq <+ IsEq <+ HasEqBool.

Module Type BooleanDecidableType <: DecidableType <: BooleanEqualityType
 := Eq <+ IsEq <+ HasEqDec <+ HasEqBool.

Module Type DecidableTypeFull <: DecidableTypeBoth <: BooleanDecidableType
 := Eq <+ IsEq <+ IsEqOrig <+ HasEqDec <+ HasEqBool.

(** Same, with notation for [eq] *)

Module Type EqualityType' := EqualityType <+ EqNotation.
Module Type EqualityTypeOrig' := EqualityTypeOrig <+ EqNotation.
Module Type EqualityTypeBoth' := EqualityTypeBoth <+ EqNotation.
Module Type DecidableType' := DecidableType <+ EqNotation.
Module Type DecidableTypeOrig' := DecidableTypeOrig <+ EqNotation.
Module Type DecidableTypeBoth' := DecidableTypeBoth <+ EqNotation.
Module Type BooleanEqualityType' :=
 BooleanEqualityType <+ EqNotation <+ EqbNotation.
Module Type BooleanDecidableType' :=
 BooleanDecidableType <+ EqNotation <+ EqbNotation.
Module Type DecidableTypeFull' := DecidableTypeFull <+ EqNotation.

(** * Compatibility wrapper from/to the old version of
      [EqualityType] and [DecidableType] *)

Module BackportEq (E:Eq)(F:IsEq E) <: IsEqOrig E.
 Definition eq_refl := F.eq_equiv.(@Equivalence_Reflexive _ _). 
 Definition eq_sym := F.eq_equiv.(@Equivalence_Symmetric _ _).
 Definition eq_trans := F.eq_equiv.(@Equivalence_Transitive _ _).
End BackportEq.

Module UpdateEq (E:Eq)(F:IsEqOrig E) <: IsEq E.
 Instance eq_equiv : Equivalence E.eq.
 Proof. exact (Build_Equivalence _ F.eq_refl F.eq_sym F.eq_trans). Qed.
End UpdateEq.

Module Backport_ET (E:EqualityType) <: EqualityTypeBoth
 := E <+ BackportEq.

Module Update_ET (E:EqualityTypeOrig) <: EqualityTypeBoth
 := E <+ UpdateEq.

Module Backport_DT (E:DecidableType) <: DecidableTypeBoth
 := E <+ BackportEq.

Module Update_DT (E:DecidableTypeOrig) <: DecidableTypeBoth
 := E <+ UpdateEq.


(** * Having [eq_dec] is equivalent to having [eqb] and its spec. *)

Module HasEqDec2Bool (E:Eq)(F:HasEqDec E) <: HasEqBool E.
 Definition eqb x y := if F.eq_dec x y then true else false.
 Lemma eqb_eq : forall x y, eqb x y = true -> E.eq x y.
 Proof.
  intros x y. unfold eqb. destruct F.eq_dec as [EQ|NEQ].
  auto with *.
  discriminate.
 Qed.
 Lemma eq_eqb : forall x y, E.eq x y -> eqb x y = true.
 Proof.
  intros x y. unfold eqb. destruct F.eq_dec as [EQ|NEQ].
  auto with *.
  intro EQ; elim NEQ; auto.
 Qed.
End HasEqDec2Bool.

Module HasEqBool2Dec (E:Eq)(F:HasEqBool E) <: HasEqDec E.
 Lemma eq_dec : forall x y, sum (E.eq x y) (E.eq x y -> False).
 Proof.
  intros x y.
  assert (Hl := F.eqb_eq). specialize Hl with x y.
  assert (Hr := F.eq_eqb). specialize Hr with x y.
  destruct (F.eqb x y); [left|right].
  apply Hl; auto.
  intro EQ. apply Hr in EQ. discriminate.
 Defined.
End HasEqBool2Dec.

Module Dec2Bool (E:DecidableType) <: BooleanDecidableType
 := E <+ HasEqDec2Bool.

Module Bool2Dec (E:BooleanEqualityType) <: BooleanDecidableType
 := E <+ HasEqBool2Dec.


(** Some properties of boolean equality *)

Module BoolEqualityFacts (Import E : BooleanEqualityType').

(** [eqb] is compatible with [eq] *)

Instance eqb_compat : Proper (E.eq ==> E.eq ==> Logic.eq) eqb.
Proof.
intros x x' Exx' y y' Eyy'.
destruct eq_equiv.
apply eq_true_iff_eq.
split ; intros H.
apply eqb_eq in H.
apply eq_eqb.
eapply Equivalence_Transitive ; try eassumption.
apply Equivalence_Symmetric in Exx'.
eapply Equivalence_Transitive ; eassumption.
apply eqb_eq in H.
apply eq_eqb.
eapply Equivalence_Transitive ; try eassumption.
apply Equivalence_Symmetric in Eyy'.
eapply Equivalence_Transitive ; eassumption.
Qed.

(* TODO
(** Alternative specification of [eqb] based on [reflect]. *)

Lemma eqb_spec x y : reflect (x==y) (x =? y).
Proof.
apply iff_reflect. symmetry. apply eqb_eq.
Defined.
*)

(** Negated form of [eqb_eq] *)

Lemma eqb_neq x y : (x =? y) = false <-> x ~= y.
Proof.
split.
intros H He.
apply eq_eqb in He.
destruct (x =? y) ; discriminate.
intros He.
assert ((x =? y) = true -> False).
intros H. apply He.
apply eqb_eq ; assumption.
destruct (x =? y).
contradiction H.
reflexivity.
reflexivity.
Qed.

(** Basic equality laws for [eqb] *)

Lemma eqb_refl x : (x =? x) = true.
Proof.
apply eq_eqb.
apply eq_equiv.
Qed.

Lemma eqb_sym x y : (x =? y) = (y =? x).
Proof.
apply eq_true_iff_eq. 
split ; intros H ; apply eqb_eq in H ; apply eq_eqb ;
  apply eq_equiv ; assumption.
Qed.

(** Transitivity is a particular case of [eqb_compat] *)

End BoolEqualityFacts.


(** * UsualDecidableType

   A particular case of [DecidableType] where the equality is
   the usual one of Coq. *)

Module Type HasUsualEq (Import T:Typ) <: HasEq T.
 Definition eq := @Logic.eq t.
End HasUsualEq.

Module Type UsualEq <: Eq := Typ <+ HasUsualEq.

Module Type UsualIsEq (E:UsualEq) <: IsEq E.
 (* No Instance syntax to avoid saturating the Equivalence tables *)
 Definition eq_equiv : Equivalence E.eq := eq_equivalence.
End UsualIsEq.

Module Type UsualIsEqOrig (E:UsualEq) <: IsEqOrig E.
 Definition eq_refl := @Logic.eq_refl E.t.
 Definition eq_sym := @Logic.eq_sym E.t.
 Definition eq_trans := @Logic.eq_trans E.t.
End UsualIsEqOrig.

Module Type UsualEqualityType <: EqualityType
 := UsualEq <+ UsualIsEq.

Module Type UsualDecidableType <: DecidableType
 := UsualEq <+ UsualIsEq <+ HasEqDec.

Module Type UsualDecidableTypeOrig <: DecidableTypeOrig
 := UsualEq <+ UsualIsEqOrig <+ HasEqDec.

Module Type UsualDecidableTypeBoth <: DecidableTypeBoth
 := UsualEq <+ UsualIsEq <+ UsualIsEqOrig <+ HasEqDec.

Module Type UsualBoolEq := UsualEq <+ HasEqBool.

Module Type UsualDecidableTypeFull <: DecidableTypeFull
 := UsualEq <+ UsualIsEq <+ UsualIsEqOrig <+ HasEqDec <+ HasEqBool.


(** Some shortcuts for easily building a [UsualDecidableType] *)

Module Type MiniDecidableType.
 Include Typ.
 Parameter eq_dec : forall x y : t, sum (x=y) (x=y -> False).
End MiniDecidableType.

Module Make_UDT (M:MiniDecidableType) <: UsualDecidableTypeBoth
 := M <+ HasUsualEq <+ UsualIsEq <+ UsualIsEqOrig.

Module Make_UDTF (M:UsualBoolEq) <: UsualDecidableTypeFull
 := M <+ UsualIsEq <+ UsualIsEqOrig <+ HasEqBool2Dec.
