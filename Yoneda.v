Require Import ssreflect ssrfun ssrbool eqtype seq.
Require Import FunctionalExtensionality.
Require Import Coq.Logic.ProofIrrelevance.
Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits. 

(** * Basic Category Theory *)

(*************************************************)
(** ** Categories                                *)
(*************************************************)

Module Category.

Section RawMixin.

(** ** A category over objects of type 'T'. *)

Record mixin_of (T : Type) := Mixin {
  mx_hom : forall a b : T, Type;    (** hom-sets *)
  (** we have an identity arrow at all types*)
  mx_id : forall a : T, mx_hom a a; 
  (** composition of arrows *)
  mx_comp : forall a b c (f : mx_hom b c) (g : mx_hom a b), mx_hom a c;
  _ : forall a b (g : mx_hom a b), mx_comp (mx_id b) g = g;
  _ : forall a b (f : mx_hom a b), mx_comp f (mx_id a) = f;
  _ : forall a b c d (f : mx_hom c d) (g : mx_hom b c) (h : mx_hom a b),
        mx_comp f (mx_comp g h) = mx_comp (mx_comp f g) h
}.

End RawMixin.

Section ClassDef.
Local Notation tp := Type.

Record class_of T := Class {mixin : mixin_of T}.

Structure type : Type := Pack {sort : tp; _ : class_of sort; _ : tp}.
Local Coercion sort : type >-> Sortclass.

Variables (T : tp) (cT : type).
Definition class := let: Pack _ c _ as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack T c T.

(* produce a category type out of the mixin *)
(* equalize m0 and m by means of a phantom *)
Definition pack (m0 : mixin_of T) := 
  fun m & phant_id m0 m => Pack (@Class T m) T.

Definition hom := mx_hom (mixin class).
Definition ida := mx_id (mixin class).
Definition comp := @mx_comp cT (mixin class).

End ClassDef.

Module Exports.
Coercion sort : type >-> Sortclass.
Notation category := Category.type.
Notation CategoryMixin := Category.Mixin.
Notation Category T m := (@pack T _ m id).

Notation "[ 'category' 'of' T 'for' cT ]" := (@clone T cT _ id)
  (at level 0, format "[ 'category'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'category' 'of' T ]" := (@clone T _ _ id)
  (at level 0, format "[ 'category'  'of'  T ]") : form_scope.

Notation hom := Category.hom.
Notation ida := Category.ida.
Notation comp := Category.comp.

Arguments Category.hom [cT] a b.
Arguments Category.ida [cT a].
Arguments Category.comp [cT a b c] _ _.
Prenex Implicits Category.comp Category.ida Category.hom.

Section Laws.
Variable C : category.

Lemma id_left (a b : C) (g : hom a b) : comp ida g = g.
Proof. by case: C a b g=> ?; case; case. Qed.

Lemma id_right (a b : C) (f : hom a b) : comp f ida = f.
Proof. by case: C a b f=> ?; case; case. Qed.

Lemma comp_assoc (a b c d : C) (f : hom c d) (g : hom b c) (h : hom a b) :
  comp f (comp g h) = comp (comp f g) h.
Proof. by case: C a b c d f g h=> ?; case; case. Qed.

End Laws.

Hint Resolve id_left id_right comp_assoc.

End Exports.

End Category.

Export Category.Exports.

(*************************************************)
(** ** Some Categories                           *)
(*************************************************)

(** *** Category of Coq [Type]s *)

Section Coq.
Notation tp := (Type).
Program Definition coqCategoryMixin := 
  @Category.Mixin tp (fun A B => A -> B)
      (fun A (a : A) => a) 
      (fun A B C (f : B -> C) (g : A -> B) => f \o g)
      _ _ _.
Definition Coq : category := 
  Eval hnf in Category tp coqCategoryMixin.
End Coq.

(*************************************************)
(** ** Functors                                  *)
(*************************************************)

Module Functor.

Section RawMixin.

Record mixin_of (C D : category) := Mixin {
  mx_fobj : forall a : C, D;
  mx_fmap : forall (a b : C) (f : hom a b), hom (mx_fobj a) (mx_fobj b);
  _ : forall a : C, mx_fmap (ida (a:=a)) = ida (a:=mx_fobj a);
  _ : forall (a b c : C) (f : hom b c) (g : hom a b),
        mx_fmap (comp f g) = comp (mx_fmap f) (mx_fmap g)
}.

End RawMixin.

Section ClassDef.

Variables C D : category.

Record class_of C D := Class {mixin : mixin_of C D}.

Structure type : Type := Pack {_ : class_of C D}.

Variables cT : type.
Definition class := let: Pack c := cT return class_of C D in c.
Definition clone c of phant_id class c := @Pack c.

Definition pack (m0 : mixin_of C D) := 
  fun m & phant_id m0 m => Pack (@Class C D m).

Definition fobj := mx_fobj (mixin class).
Definition fmap := mx_fmap (mixin class).

End ClassDef.

Module Exports.
Notation functor := Functor.type.
Notation FunctorMixin := Functor.Mixin.
Notation Functor C D m := (@pack C D _ m id).

Notation "[ 'functor' 'of' C D 'for' cT ]" := (@clone C D cT _ id)
  (at level 0, format "[ 'functor'  'of'  C  D  'for'  cT ]") : form_scope.
Notation "[ 'functor' 'of' C D ]" := (@clone C D _ _ id)
  (at level 0, format "[ 'functor'  'of'  C  D ]") : form_scope.

Notation fobj := Functor.fobj.
Notation fmap := Functor.fmap.

Arguments Functor.fobj [C D] cT _.
Arguments Functor.fmap [C D] cT [a b] _.

Section Laws.
Variables C D : category.
Variable F : functor C D.

Lemma fmap_id (a : C) : fmap F (ida (a:=a)) = ida.
Proof. by case: F; case; case. Qed.

Lemma fmap_assoc (a b c : C) (f : hom b c) (g : hom a b) :
  fmap F (comp f g) = comp (fmap F f) (fmap F g).
Proof. by case: F; case; case. Qed.
 
End Laws.

Hint Resolve fmap_id fmap_assoc.

End Exports.

End Functor.

Export Functor.Exports.

(*************************************************)
(** ** Some Functors                             *)
(*************************************************)

(** *** T -> Option T *)

Section OptionFunctor.
Notation tp := (option).
Program Definition optionFunctorMixin := 
  @Functor.Mixin Coq Coq tp 
    (fun _ _ f o => if o is Some v then Some (f v)
                    else None) _ _.
Next Obligation. by extensionality x; case: x. Qed.
Next Obligation. by extensionality x; case: x. Qed.
Canonical optionFunctor : functor Coq Coq := 
  Eval hnf in Functor Coq Coq optionFunctorMixin.
End OptionFunctor.

(** *** T -> List T *)

Section ListFunctor.
Notation tp := (list).
Program Definition listFunctorMixin := 
  @Functor.Mixin Coq Coq tp (fun _ _ f l => map f l) _ _.
Next Obligation. by extensionality x; elim: x=> // ? l /= ->. Qed.
Next Obligation. by extensionality x; elim: x=> // ? l /= ->. Qed.
Canonical listFunctor : functor Coq Coq := 
  Eval hnf in Functor Coq Coq listFunctorMixin.
End ListFunctor.

(** *** hom(A,--) *)

Section HomFunctor.
Variable C : category.
Variable a : C.
Notation tp := (fun r => hom a r).
Program Definition homFunctorMixin := 
  @Functor.Mixin C Coq tp (fun _ _ f g => comp f g) _ _.
Next Obligation. by extensionality x; rewrite id_left. Qed.
Next Obligation. by extensionality x; rewrite -comp_assoc. Qed.
Canonical homFunctor : functor C Coq := 
  Eval hnf in Functor C Coq homFunctorMixin.

Lemma hom_fmap (b c : C) (f : hom b c) (g : fobj homFunctor b) : 
  fmap homFunctor f g = comp f g.
Proof. by rewrite /homFunctor /= /homFunctorMixin /Functor.fmap. Qed.

End HomFunctor.

Arguments homFunctor [C] _.

Notation "a '==>' '?'" := (homFunctor a)
  (at level 50, format "a  '==>'  '?'") : form_scope.

(*************************************************)
(** ** Natural Transformations                   *)
(*************************************************)

Module Natural.

Section RawMixin.
Variables C D : category.
Variables F G : functor C D.

Record mixin_of := Mixin {
  mx_phi : forall a : C, hom (fobj F a) (fobj G a);
  _ : forall (a b : C) (f : hom a b),
        comp (mx_phi b) (fmap F f) = comp (fmap G f) (mx_phi a)
}.

End RawMixin.

Section ClassDef.
Variables C D : category.
Variables F G : functor C D.

Record class_of C D (F G : functor C D) := Class {mixin : mixin_of F G}.

Structure type : Type := Pack {_ : class_of F G}.

Variable cT : type.
Definition class := let: Pack c as cT' := cT return class_of F G in c.
Definition clone c of phant_id class c := @Pack c.

Definition pack (m0 : mixin_of F G) := 
  fun m & phant_id m0 m => Pack (@Class C D F G m).

Definition phi := mx_phi (mixin class).

End ClassDef.

Module Exports.
Coercion phi : type >-> Funclass.
Notation natural := Natural.type.
Notation NaturalMixin := Natural.Mixin.
Notation Natural F G m := (@pack _ _ F G _ m id).

Notation "[ 'natural' 'of' F G 'for' cT ]" := (@clone F G cT _ id)
  (at level 0, format "[ 'natural'  'of'  F  G  'for'  cT ]") : form_scope.
Notation "[ 'natural' 'of' F G ]" := (@clone F G _ _ id)
  (at level 0, format "[ 'natural'  'of'  F  G ]") : form_scope.
Notation "F ~~> G" := (natural F G)
  (at level 60, format "F  '~~>'  G") : form_scope.

Notation phi := Natural.phi.

Arguments Natural.phi [C D] F G [cT] _.

Section Laws.
Variables C D : category.
Variables F G : functor C D.
Variable phi : F ~~> G.

Lemma phi_natural (a b : C) (f : hom a b) :
  comp (phi b) (fmap F f) = comp (fmap G f) (phi a).
Proof. by case: phi=> [][][]. Qed.

End Laws.

Section Extensionality.
Variables C D : category.
Variables F G : functor C D.
Variable phi1 phi2 : natural F G.

Lemma phi_extensionality : (forall r, phi1 r = phi2 r) -> phi1 = phi2.
Proof.
move=> H; destruct phi1, phi2.
destruct c, c0; destruct mixin0, mixin1; f_equal; f_equal.
have Heq: mx_phi0 = mx_phi1.
{ by extensionality r; apply: (H r). }
by subst; f_equal; apply proof_irrelevance.
Qed.

End Extensionality.  

Hint Resolve phi_natural.

End Exports.

End Natural.

Export Natural.Exports.

(*************************************************)
(** ** Cones                                     *)
(*************************************************)

Module Cone.

Section RawMixin.
Variables J C : category.
Variable F : functor J C.

Record mixin_of := Mixin {
  mx_cone : C;
  mx_mor : forall j : J, hom mx_cone (fobj F j);
  _ : forall (j k : J) (f : hom (fobj F j) (fobj F k)), 
        comp f (mx_mor j) = mx_mor k
}.

End RawMixin.

Section ClassDef.

Variables J C : category.

Variable F : functor J C.

Record class_of (J C : category) (F : functor J C) := 
  Class {mixin : mixin_of F}.

Structure type : Type := Pack {_ : class_of F}.

Variables cT : type.
Definition class := let: Pack c := cT return class_of F in c.
Definition clone c of phant_id class c := @Pack c.

Definition pack (m0 : mixin_of F) := 
  fun m & phant_id m0 m => Pack (@Class J C F m).

Definition cone := mx_cone (mixin class).
Definition mor := mx_mor (mixin class).

End ClassDef.

Module Exports.
Coercion cone : type >-> Category.sort.
Notation cone := Cone.type.
Notation ConeMixin := Cone.Mixin.
Notation Cone J C F m := (@pack J C F _ m id).

Notation "[ 'cone' 'of' J C F 'for' cT ]" := (@clone J C F cT _ id)
  (at level 0, format "[ 'cone'  'of'  J  C  F  'for'  cT ]") : form_scope.
Notation "[ 'cone' 'of' J C F ]" := (@clone J C F _ _ id)
  (at level 0, format "[ 'cone'  'of'  J  C  F ]") : form_scope.

Notation cone_head := Cone.cone.
Notation cone_mor := Cone.mor.

Arguments Cone.cone [J C F] cT.
Arguments Cone.mor [J C F] cT j.

Section Laws.
Variables J C : category.
Variable F : functor J C.
Variable Con : cone F.

Lemma cone_commutes (j k : J) (f : hom (fobj F j) (fobj F k)) :
  comp f (cone_mor Con j) = cone_mor Con k.
Proof. by case: Con; case; case. Qed.
 
End Laws.

Hint Resolve cone_commutes.

End Exports.

End Cone.

Export Cone.Exports.

(*************************************************)
(** ** Limits                                    *)
(*************************************************)

Module Limit.

Section RawMixin.
Variables J C : category.
Variable F : functor J C.

Record mixin_of := Mixin {
  mx_lim : cone F;
  _ : forall Con : cone F, 
        exists! f : hom Con mx_lim, 
        forall j : J, comp (cone_mor mx_lim j) f = cone_mor Con j
}.

End RawMixin.

Section ClassDef.

Variables J C : category.

Variable F : functor J C.

Record class_of (J C : category) (F : functor J C) := 
  Class {mixin : mixin_of F}.

Structure type : Type := Pack {_ : class_of F}.

Variable cT : type.
Definition class := let: Pack c := cT return class_of F in c.
Definition clone c of phant_id class c := @Pack c.

Definition pack (m0 : mixin_of F) := 
  fun m & phant_id m0 m => Pack (@Class J C F m).

Definition lim := mx_lim (mixin class).

End ClassDef.

Module Exports.
Coercion lim : type >-> Cone.type.
Notation limit := Limit.type.
Notation LimitMixin := Limit.Mixin.
Notation Limit J C F m := (@pack J C F _ m id).

Notation "[ 'lim' 'of' J C F 'for' cT ]" := (@clone J C F cT _ id)
  (at level 0, format "[ 'lim'  'of'  J  C  F  'for'  cT ]") : form_scope.
Notation "[ 'lim' 'of' J C F ]" := (@clone J C F _ _ id)
  (at level 0, format "[ 'lim'  'of'  J  C  F ]") : form_scope.

Notation lim := Limit.lim.

Arguments Limit.lim [J C F] cT.

Section Laws.
Variables J C : category.
Variable F : functor J C.
Variable Lim : limit F.

Lemma limit_universal (Con : cone F) :
  exists! f : hom Con Lim,
  forall j : J, comp (cone_mor Lim j) f = cone_mor Con j.
Proof. by case: Lim; case; case. Qed.
 
End Laws.

Hint Resolve limit_universal.

End Exports.

End Limit.

Export Limit.Exports.

(*************************************************)
(** ** Isomorphisms                              *)
(*************************************************)

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

(*************************************************)
(** ** Yoneda                                    *)
(*************************************************)
 
Section Yoneda.
Variable C : category.
Variable F : functor C Coq.

Definition Y (a : C) := (a ==> ?) ~~> F.

Definition uncheck a (y : Y a) : fobj F a := y a ida.

Section check.
  Variables (a : C) (x : fobj F a).
  Definition check_phi (r : C) (f : fobj (a ==> ?) r) := fmap F f x.

  Lemma check_phi_natural (r b : C) (f : hom r b) :
    check_phi (r:=b) \o fmap (a ==> ?) f = fmap F f \o check_phi (r:=r).
  Proof. by extensionality y; rewrite /check_phi /= hom_fmap fmap_assoc. Qed.

  Definition checkNaturalMixin := 
    @Natural.Mixin C Coq (a ==> ?) F check_phi check_phi_natural.
  Definition check : Y a := 
    Eval hnf in Natural (a ==> ?) F checkNaturalMixin.
End check.

Lemma checkP a r (x : fobj F a) (f : fobj (a ==> ?) r) :
  check x _ f = fmap F f x.
Proof. by []. Qed.

Lemma uncheck_check a x : uncheck (a:=a) (check (a:=a) x) = id x.
Proof. by rewrite /uncheck /funcomp checkP fmap_id. Qed.

Lemma check_uncheck' A (y : Y A) R g : check (uncheck y) R g = y R g.
Proof.
rewrite checkP /uncheck.
suff: (comp (fmap F g) (y A)) ida = y R g => //.
rewrite -phi_natural.
suff: (y R \o fmap (A ==> ?) g) ida = y R g=> //=.
by rewrite hom_fmap id_right.
Qed.

Lemma check_uncheck A (y : Y A) : check (uncheck y) = y.
Proof. 
by apply: phi_extensionality=> r; extensionality x; apply: check_uncheck'. 
Qed.

End Yoneda. 

(*
Section YonedaIso.
Variable C : category.
Variable F : functor C Coq.
Set Printing Universes.

(** Can't typecheck the following due to a universe inconsistency: 
  Don't know that univ(Y F a) <= univ(T) in IsoMixin T U ...*)

Definition YonedaIsoMixin (a : C) := 
  @IsoMixin (Y F a) (fobj F a) (@uncheck _ F a) (@check _ F a) 
            (@check_uncheck _ F a) (@uncheck_check _ F a).
Canonical YonedaIso a := @Iso (Y F a) (F a) (YonedaIsoMixin a).

End YonedaIso.
*)


