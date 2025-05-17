import Mathlib

open Localization

variable (A B : Type*) [CommRing A] [CommRing B]
variable (S : Submonoid A) (T : Submonoid B)

lemma units_mul {a : A} {b : B} (ha : IsUnit a) (hb : IsUnit b) : IsUnit (a, b) :=
  ⟨⟨(a, b), (↑ha.unit⁻¹, ↑hb.unit⁻¹), by simp, by simp⟩, rfl⟩

instance : Algebra (A × B) (Localization S × Localization T) :=
  RingHom.toAlgebra (RingHom.prod
    ((algebraMap A (Localization S)).comp (RingHom.fst A B))
    ((algebraMap B (Localization T)).comp (RingHom.snd A B)))

noncomputable def localizationCommutesWithProduct
  (A B : Type*) [CommRing A] [CommRing B] (S : Submonoid A) (T : Submonoid B):
    (Localization S × Localization T) ≃ₐ[A × B] (Localization (S.prod T)) := by

  let f : A × B →+* Localization S := (algebraMap A (Localization S)).comp (RingHom.fst A B)
  let g : A × B →+* Localization T := (algebraMap B (Localization T)).comp (RingHom.snd A B)
  let φ : A × B →+* Localization S × Localization T := RingHom.prod f g
  let ψ := algebraMap (A × B) (Localization S × Localization T)

  have h_φst_units : ∀ (a : S.prod T), IsUnit (algebraMap (A × B) (Localization S × Localization T) a) := by
    intro ⟨⟨s, t⟩, hs, ht⟩
    have fs_unit : IsUnit (algebraMap (A × B) (Localization S × Localization T) (s, t)).1 :=
      IsLocalization.map_units (Localization S) ⟨s, hs⟩

    have gt_unit : IsUnit (algebraMap (A × B) (Localization S × Localization T) (s, t)).2 :=
      IsLocalization.map_units (Localization T) ⟨t, ht⟩

    exact units_mul (Localization S) (Localization T) fs_unit gt_unit

  have kernel_eq_zero_divisors : ∀ {x y : A × B}, ψ x = ψ y → ∃ (c : S.prod T), c * x = c * y := by
    intro x y ψx_eq_ψy
    obtain ⟨s, hs⟩ := (IsLocalization.eq_iff_exists S (Localization S)).mp (congr_arg Prod.fst ψx_eq_ψy)
    obtain ⟨t, ht⟩ := (IsLocalization.eq_iff_exists T (Localization T)).mp (congr_arg Prod.snd ψx_eq_ψy)
    let st : S.prod T := ⟨(s, t), s.prop, t.prop⟩
    use st
    exact Prod.ext hs ht

  have h_φ_epic : ∀ (c : Localization S × Localization T), ∃ (d : (A × B) × (S.prod T)), c * ψ d.2 = ψ d.1 := by
    intro c
    have (φa, φb) := c
    have φa_eq_a_over_s : ∃ (s: S) (a: A), ((algebraMap A (Localization S)) s) * φa = (algebraMap A (Localization S)) a := by
      let ⟨(a, s), h⟩ := IsLocalization.surj S φa
      use s
      use a
      rw [mul_comm, h]
    have φb_eq_b_over_t : ∃ (t: T) (b: B), ((algebraMap B (Localization T)) t) * φb = (algebraMap B (Localization T)) b := by
      let ⟨(b, t), h⟩ := IsLocalization.surj T φb
      use t
      use b
      rw [mul_comm, h]
    obtain ⟨s, a, hsa⟩ := φa_eq_a_over_s
    obtain ⟨t, b, htb⟩ := φb_eq_b_over_t
    let d : A × B := (a, b)
    let st : S.prod T := ⟨(s, t), s.prop, t.prop⟩
    use (d, st)
    calc
      (φa, φb) * ψ ↑st = ψ ↑st * (φa, φb) := by rw [mul_comm]
      _ =  ((algebraMap A (Localization S)) s, (algebraMap B (Localization T)) t) * (φa, φb) := rfl
      _ = ((algebraMap A (Localization S)) s * φa,  (algebraMap B (Localization T)) t * φb) := rfl
      _ = ((algebraMap A (Localization S)) a, (algebraMap B (Localization T)) b) := by rw [hsa, htb]
      _ = φ (a, b) := rfl
      _ = φ d := rfl
      _ = ψ d := rfl


  -- Now construct the IsLocalization instance
  haveI : IsLocalization (S.prod T) (Localization S × Localization T) := {
    map_units' := h_φst_units,
    surj' := h_φ_epic,
    exists_of_eq := kernel_eq_zero_divisors
  }

  exact IsLocalization.algEquiv (S.prod T) (Localization S × Localization T) (Localization (S.prod T))
