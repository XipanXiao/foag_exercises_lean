import Mathlib

open CategoryTheory

universe u

variable {C : Type u} [Category C]
variable (A : C)

/-- The type of invertible endomorphisms of A -/
def Aut' (A : C) := { f : A ⟶ A // IsIso f }

namespace Aut'

instance : One (Aut' A) where
  one := ⟨𝟙 A, inferInstance⟩

lemma one_def : (1 : Aut' A).val = 𝟙 A := rfl

instance : Mul (Aut' A) where
  mul f g := ⟨f.val ≫ g.val, by refine IsIso.comp_isIso' f.property g.property⟩

lemma mul_def (f g : Aut' A) : (f * g).val = f.val ≫ g.val := rfl

@[ext]
lemma ext {f g : Aut' A} (h : f.val = g.val) : f = g := Subtype.ext h

/-- Proof that Aut'(A) forms a group under composition -/
noncomputable instance : Group (Aut' A) where
  mul_assoc a b c := by
    apply Subtype.ext
    exact Category.assoc a.val b.val c.val

  one_mul a := by
    apply Subtype.ext
    exact Category.id_comp a.val

  mul_one a := by
    apply Subtype.ext
    exact Category.comp_id a.val

  inv a := ⟨@inv _ _ _ _ a.val a.property, a.property.inv_isIso⟩

  inv_mul_cancel a := by
    apply Subtype.ext
    rw [mul_def, one_def]
    simp

def toFun {A B : C} (φ : A ≅ B) (f: CategoryTheory.Aut A) : CategoryTheory.Aut B := ⟨
  φ.inv ≫ f.hom ≫ φ.hom,
  φ.inv ≫ f.inv ≫ φ.hom,
  by simp,
  by simp
⟩

def invFun {A B : C} (φ : A ≅ B) (g: CategoryTheory.Aut B) : CategoryTheory.Aut A := ⟨
  φ.hom ≫ g.hom ≫ φ.inv,
  φ.hom ≫ g.inv ≫ φ.inv,
  by simp,
  by simp
⟩

lemma to_inv_compose {A B : C} {φ : A ≅ B} {g: CategoryTheory.Aut B } : toFun φ (invFun φ g) = g := by
    calc
      toFun φ (invFun φ g) = ⟨
        φ.inv ≫ (φ.hom ≫ g.hom ≫ φ.inv) ≫ φ.hom,
        φ.inv ≫ (φ.hom ≫ g.inv ≫ φ.inv) ≫ φ.hom,
        by simp,
        by simp
      ⟩ := by rfl
      _ = ⟨
        g.hom,
        g.inv,
        by simp,
        by simp
      ⟩ := by simp
      _ = g := rfl

lemma inv_to_compose {A B : C} {φ : A ≅ B} {f: CategoryTheory.Aut A } : invFun φ (toFun φ f) = f := by
    calc
      invFun φ (toFun φ f) = ⟨
        φ.hom ≫ (φ.inv ≫ f.hom ≫ φ.hom) ≫ φ.inv,
        φ.hom ≫ (φ.inv ≫ f.inv ≫ φ.hom) ≫ φ.inv,
        by simp,
        by simp
            ⟩ := by rfl
      _ = ⟨
        f.hom,
        f.inv,
        by simp,
        by simp
      ⟩ := by simp
      _ = f := rfl

lemma map_mul' {A B : C} {φ : A ≅ B} (f g: CategoryTheory.Aut A) : toFun φ (f * g) = toFun φ f * toFun φ g := by
    calc
      toFun φ (f * g) = ⟨
        φ.inv ≫ ((f * g).hom) ≫ φ.hom,
        φ.inv ≫ ((f * g).inv) ≫ φ.hom,
        by simp,
        by simp
      ⟩ := by rfl
      _ = ⟨
        φ.inv ≫ (g.hom ≫ f.hom) ≫ φ.hom,
        φ.inv ≫ (f.inv ≫ g.inv) ≫ φ.hom,
        by simp,
        by simp
      ⟩ := by rfl
      _ = ⟨
        (φ.inv ≫ g.hom ≫ φ.hom) ≫ (φ.inv ≫ f.hom ≫ φ.hom),
        (φ.inv ≫ f.inv ≫ φ.hom) ≫ (φ.inv ≫ g.inv ≫ φ.hom),
        by simp,
        by simp
      ⟩ := by simp
      _ = toFun φ f * toFun φ g := by rfl

/--  Show that two isomorphic objects have isomorphic automorphism groups.  -/
example {A B : C} (φ : A ≅ B) : CategoryTheory.Aut A ≃* CategoryTheory.Aut B :=
  { toFun := toFun φ,
    invFun := invFun φ,
    left_inv := fun f => by exact inv_to_compose
    right_inv := fun f => by exact to_inv_compose
    map_mul' := map_mul'
    }
