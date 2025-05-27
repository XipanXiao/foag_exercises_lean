import Mathlib
open scoped TensorProduct DirectSum

variable {R : Type*} [CommRing R]
variable {ι : Type*} [DecidableEq ι]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {N : ι → Type*} [∀ i, AddCommGroup (N i)] [∀ i, Module R (N i)]

noncomputable def tensorDirectSum :
    M ⊗[R] (⨁ i, N i) ≃ₗ[R] ⨁ i, M ⊗[R] N i :=
  LinearEquiv.ofLinear
    -- forward direction
    (TensorProduct.lift
      { toFun := fun m ↦
          DirectSum.toModule R _ _ fun i ↦
            (DirectSum.lof R ι (fun i ↦ M ⊗[R] N i) i).comp
              ((TensorProduct.mk R M (N i)) m)
        map_add' := by
          intros m₁ m₂
          ext i x
          simp
        map_smul' := by
          intros r m
          ext i x
          simp
      })
    -- backward direction
    (DirectSum.toModule R _ _ fun i ↦
      TensorProduct.map LinearMap.id (DirectSum.lof R ι N i))
    -- forward ∘ backward = id
    (by
      ext i x m
      simp
    )
    -- backward ∘ forward = id
    (by
      ext i x m
      simp
      )
