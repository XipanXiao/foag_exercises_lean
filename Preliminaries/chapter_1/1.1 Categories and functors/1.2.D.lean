import Mathlib

open Localization

variable {A : Type*} [CommRing A]
variable (S : Submonoid A)
abbrev AS := Localization S

-- Universal property of the localization A → S⁻¹A
theorem localization_universal_property
  {B : Type*} [CommRing B] [Algebra A B]
  (h : ∀ s : S, IsUnit (algebraMap A B s)) :
  ∃! (f : AS S →+* B), f.comp (algebraMap A (AS S)) = algebraMap A B := by
  have h₁ : ∀ s : S, IsUnit (algebraMap A B s) := h
  have h₂ : ∃! (f : AS S →+* B), f.comp (algebraMap A (AS S)) = algebraMap A B := by
    -- Use the universal property of the localization to find a unique ring homomorphism
    -- from the localization to B that agrees with the given condition.
    refine' ⟨IsLocalization.lift (h₁), _, _⟩
    · -- Show that the lifted homomorphism satisfies the condition
      ext
      simp [IsLocalization.lift_eq]
    · -- Show the uniqueness of the lifted homomorphism
      intro f hf
      have h₃ : f.comp (algebraMap A (AS S)) = algebraMap A B := hf
      have h₄ : f = IsLocalization.lift (h₁) := by
        apply IsLocalization.ringHom_ext S
        simp_all [IsLocalization.lift_eq]
      rw [h₄]
  -- Use the derived result to conclude the proof.
  exact h₂
