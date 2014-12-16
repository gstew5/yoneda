Require Import ssreflect ssrfun ssrbool eqtype seq.
Require Import FunctionalExtensionality.
Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits. 

(** * Proof of the Yoneda Lemma *)

(** ** Functors *)

Module Functor.

Section RawMixin.

Record mixin_of (F : Type -> Type) := Mixin {
  mx_fmap : forall A B : Type, (A -> B) -> F A -> F B;
  _ : forall (A : Type) (x : F A), mx_fmap (fun a => a) x = x; 
  _ : forall (A B C : Type) (f : A -> B) (g : B -> C) (x : F A),
          mx_fmap (g \o f) x = (mx_fmap g \o mx_fmap f) x
}.

End RawMixin.

Section ClassDef.
Local Notation tp := (Type -> Type).

Record class_of F := Class {mixin : mixin_of F}.

Structure type : Type := Pack {sort : tp; _ : class_of sort; _ : tp}.
Local Coercion sort : type >-> Funclass.

Variables (F : tp) (cT : type).
Definition class := let: Pack _ c _ as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack F c F.

(* produce a functor type out of the mixin *)
(* equalize m0 and m by means of a phantom *)
Definition pack (m0 : mixin_of F) := 
  fun m & phant_id m0 m => Pack (@Class F m) F.

Definition fmap := mx_fmap (mixin class).

End ClassDef.

Module Exports.
Coercion sort : type >-> Funclass.
Notation functor := Functor.type.
Notation FunctorMixin := Functor.Mixin.
Notation Functor F m := (@pack F _ m id).

Notation "[ 'functor' 'of' F 'for' cT ]" := (@clone F cT _ id)
  (at level 0, format "[ 'functor'  'of'  F  'for'  cT ]") : form_scope.
Notation "[ 'functor' 'of' F ]" := (@clone F _ _ id)
  (at level 0, format "[ 'functor'  'of'  F ]") : form_scope.

Notation fmap := Functor.fmap.

Arguments Functor.fmap [cT A B] _ _.
Prenex Implicits Functor.fmap.

Section Laws.
Variable F : functor.

Lemma fmap_id (A : Type) (x : F A) : fmap id x = x.
Proof. by case: F x=>S [[]]. Qed.

Lemma fmap_assoc (A B C : Type) (f : A -> B) (g : B -> C) (x : F A) :
  fmap (g \o f) x = (fmap g \o fmap f) x.
Proof. by case: F x=>S [[]]. Qed.
 
End Laws.

Hint Resolve fmap_id.

End Exports.

End Functor.

Export Functor.Exports.

Section RightFunctor.
Variable A : Type.

Notation tp := (fun R => A -> R).

Program Definition rightFunctorMixin := 
  @Functor.Mixin tp (fun _ _ f g => f \o g) _ _.
Definition rightFunctor : functor := 
  Eval hnf in Functor tp rightFunctorMixin.

Lemma right_fmap (B C : Type) (f : B -> C) (g : rightFunctor B) :
  fmap f g = f \o g.
Proof. by rewrite /rightFunctor /= /rightFunctorMixin /Functor.fmap. Qed.

End RightFunctor.

Notation "A '==>' '?'" := (rightFunctor A)
  (at level 50, format "A  '==>'  '?'") : form_scope.

(** ** Natural Transformations \eta *)

Module Natural.

Section RawMixin.

Variables F G : functor.

Record mixin_of := Mixin {
  mx_eta : forall A : Type, F A -> G A;
  _ : forall (A B : Type) (f : A -> B) (x : F A), 
          mx_eta (fmap f x) = fmap f (mx_eta x) 
}.

End RawMixin.

Section ClassDef.

Variables F G : functor.

Record class_of F G := Class {mixin : mixin_of F G}.

Structure type : Type := Pack {_ : class_of F G}.

Variable cT : type.
Definition class := let: Pack c as cT' := cT return class_of F G in c.
Definition clone c of phant_id class c := @Pack c.

(* produce a natural type out of the mixin *)
(* equalize m0 and m by means of a phantom *)
Definition pack (m0 : mixin_of F G) := 
  fun m & phant_id m0 m => Pack (@Class F G m).

Definition eta := mx_eta (mixin class).

End ClassDef.

Module Exports.
Coercion eta : type >-> Funclass.
Notation natural := Natural.type.
Notation NaturalMixin := Natural.Mixin.
Notation Natural F G m := (@pack F G _ m id).

Notation "[ 'natural' 'of' F G 'for' cT ]" := (@clone F G cT _ id)
  (at level 0, format "[ 'natural'  'of'  F  G  'for'  cT ]") : form_scope.
Notation "[ 'natural' 'of' F G ]" := (@clone F G _ _ id)
  (at level 0, format "[ 'natural'  'of'  F  G ]") : form_scope.
Notation "F ~~> G" := (natural F G)
  (at level 60, format "F  '~~>'  G") : form_scope.

Notation eta := Natural.eta.

Arguments Natural.eta F G [cT] [A] _.

Section Laws.
Variables F G : functor.
Variable eta : natural F G.

Lemma eta_natural (A B : Type) (f : A -> B) (x : F A) : 
  eta B (fmap f x) = fmap f (eta A x).
Proof. by case: eta=> [][][]. Qed.

End Laws.

Section Extensionality.
Variables F G : functor.
Variable eta1 eta2 : natural F G.

Lemma eta_extensionality : 
  (forall R g, eta1 R g = eta2 R g) -> eta1 = eta2.
Proof.
Admitted.

End Extensionality.  

Hint Resolve eta_natural.

End Exports.

End Natural.

Export Natural.Exports.

(** ** Isomorphisms *)

Module Iso.

Section RawMixin.

Record mixin_of (T U : Type) := Mixin {
  mx_f : T -> U;
  mx_g : U -> T;
  _ : forall t, (mx_g \o mx_f) t = t;
  _ : forall u, (mx_f \o mx_g) u = u
}.

End RawMixin.

Section ClassDef.

Variables T U : Type.

Record class_of T U := Class {mixin : mixin_of T U}.

Structure type : Type := Pack {_ : class_of T U}.

Variable cT : type.
Definition class := let: Pack c as cT' := cT return class_of T U in c.
Definition clone c of phant_id class c := @Pack c.

(* produce a natural type out of the mixin *)
(* equalize m0 and m by means of a phantom *)
Definition pack (m0 : mixin_of T U) := 
  fun m & phant_id m0 m => Pack (@Class T U m).

Definition iso_f := mx_f (mixin class).
Definition iso_g := mx_g (mixin class).

End ClassDef.

Module Exports.
Notation iso := Iso.type.
Notation IsoMixin := Iso.Mixin.
Notation Iso T U m := (@pack T U _ m id).

Notation "[ 'iso' 'of' T U 'for' cT ]" := (@clone T U cT _ id)
  (at level 0, format "[ 'iso'  'of'  T  U  'for'  cT ]") : form_scope.
Notation "[ 'iso' 'of' T U ]" := (@clone T U _ _ id)
  (at level 0, format "[ 'iso'  'of'  T  U ]") : form_scope.
Notation "T ~= U" := (iso T U)
  (at level 60, format "T  '~='  U") : form_scope.

Notation iso_f := Iso.iso_f.
Notation iso_g := Iso.iso_g.

Arguments Iso.iso_f [T U] cT t.
Arguments Iso.iso_g [T U] cT u.

Section Laws.
Variables T U : Type.
Variable iso : iso T U.

Lemma iso_gf (t : T) : (iso_g iso \o iso_f iso) t = t.
Proof. by case: iso=> [][][]. Qed.

Lemma iso_fg (u : U) : (iso_f iso \o iso_g iso) u = u.
Proof. by case: iso=> [][][]. Qed.

End Laws.

Hint Resolve iso_gf iso_fg.

End Exports.

End Iso.

Export Iso.Exports.
 
Section Yoneda.
Variable F : functor.

Definition Y (A : Type) := (A ==> ?) ~~> F.

Definition uncheck A (y : Y A) : F A := y A (fun a => a).

Section check.
  Variables (A : Type) (x : F A).

  Definition check_eta (R : Type) (f : (A ==> ?) R) := fmap f x.

  Lemma check_eta_natural (R B : Type) (f : R -> B) (y : (A ==> ?) R) :
    check_eta (fmap f y) = fmap f (check_eta y).
  Proof. by rewrite /check_eta right_fmap fmap_assoc. Qed.

  Definition checkNaturalMixin :=
    @Natural.Mixin _ F check_eta check_eta_natural.
  Definition check : Y A := 
    Eval hnf in Natural (rightFunctor A) F checkNaturalMixin.
End check.

Lemma checkP A R (x : F A) (f : rightFunctor A R) : 
  check x _ f = fmap f x.
Proof. by []. Qed.

Lemma uncheck_check A (x : F A) : uncheck (check x) = x.
Proof. by rewrite /uncheck checkP fmap_id. Qed.

Lemma check_uncheck' A (y : Y A) R g : check (uncheck y) R g = y R g.
Proof. by rewrite /uncheck checkP -eta_natural right_fmap. Qed.

Lemma check_uncheck A (y : Y A) : check (uncheck y) = y.
Proof. by apply: eta_extensionality=> R g; apply: check_uncheck'. Qed.

End Yoneda.

Section YonedaIso.
Variable F : functor.

Definition YonedaIsoMixin (A : Type) := 
  @IsoMixin (Y F A) (F A) (@uncheck F A) (@check F A) 
            (@check_uncheck F A) (@uncheck_check F A).
Definition YonedaIso (A : Type) := @Iso (Y F A) (F A) (YonedaIsoMixin A).

End YonedaIso.

