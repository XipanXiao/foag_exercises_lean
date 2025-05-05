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
