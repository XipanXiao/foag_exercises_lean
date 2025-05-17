import Mathlib

open Function

variable {A : Type*} [CommRing A]
variable {S : Submonoid A}
variable {T : Type*} [CommRing T] [Algebra A T]
variable [IsLocalization S T]

theorem algebraMap_injective_iff_no_zero_divisors :
    Injective (algebraMap A T) ↔ ∀ (s : S) (a : A), ↑s * a = 0 → a = 0 := by
  constructor
  · -- (→) If algebraMap is injective, then no s ∈ S is a zero divisor
    intro h_inj s a hsa
    apply h_inj
    rw [map_zero]
    rw [IsLocalization.map_eq_zero_iff S T]
    use s
  · -- (←) If s * a = 0 ⇒ a = 0, then algebraMap is injective
    intro h_zero_free a b heq
    have sa_eq_sb : ∃ s: S, s * a = s * b := by apply IsLocalization.exists_of_eq heq
    obtain ⟨s, hs⟩ := sa_eq_sb
    have : s * (a - b) = 0 := by rw [mul_sub_left_distrib, hs, sub_self]
    have : a - b = 0 := by exact h_zero_free s (a - b) this
    exact eq_of_sub_eq_zero this
