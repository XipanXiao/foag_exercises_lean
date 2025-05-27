import Mathlib

open CategoryTheory

universe u

variable {X Y Z : Type u} (α : X → Z) (β : Y → Z)

-- Define the fibered product as a type
def fiberedProduct : Type u := { p : X × Y // α p.1 = β p.2 }

namespace fiberedProduct

variable {α β}

-- The two projection maps
def fst : fiberedProduct α β → X := fun p => p.val.1
def snd : fiberedProduct α β → Y := fun p => p.val.2


-- Universal property (i.e., fiberedProduct is a pullback)
def lift {W : Type u} (f : W → X) (g : W → Y) (h : ∀ w, α (f w) = β (g w)) :
    W → fiberedProduct α β := fun w => ⟨(f w, g w), h w⟩

-- Uniqueness of the mediating map
lemma uniq {W : Type u} (f : W → X) (g : W → Y) (h) (φ : W → fiberedProduct α β)
    (h₁ : ∀ w, fst (φ w) = f w) (h₂ : ∀ w, snd (φ w) = g w) :
    φ = lift f g h := by
  funext w
  apply Subtype.ext
  simp only [lift, fst, snd, h₁, h₂]
  exact Prod.ext (h₁ w) (h₂ w)

end fiberedProduct
