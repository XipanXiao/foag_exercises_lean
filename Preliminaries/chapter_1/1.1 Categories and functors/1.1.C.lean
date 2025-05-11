import Mathlib

open CategoryTheory

variable (k : Type*) [Field k]

def doubleDual : FGModuleCat k ⥤ FGModuleCat k where
  obj V := FGModuleCat.of k (Module.Dual k (Module.Dual k V))
  map f := FGModuleCat.ofHom (LinearMap.dualMap (LinearMap.dualMap f.hom))

instance instFiniteOfFGModuleCat (V : FGModuleCat k) : Module.Finite k V.obj := V.property

def identityFDVec : FGModuleCat k ⥤ FGModuleCat k where
  obj := id
  map := id

-- The natural transformation η, from the identity functor to the double dual functor.
def η (V : FGModuleCat k) : V ⟶ (FGModuleCat.of k (Module.Dual k (Module.Dual k V))) :=
  FGModuleCat.ofHom {
    toFun := fun v => {
      toFun := fun g => g v,
      map_add' := fun g₁ g₂ => by simp,
      map_smul' := fun a g => by simp,
    },
    map_add' := fun v₁ v₂ => by ext; simp,
    map_smul' := fun a v => by ext; simp,
  }

-- The underlying mapping of the inverse of the natural transformation η
noncomputable def η_inv_fun (V : FGModuleCat k)
  (f : Module.Dual k (Module.Dual k V)) : V :=
  let b := Basis.ofVectorSpace k (↑V)
  ∑ i, f (b.coord i) • b i

-- Verifies that η_inv_fun is a linear map: additions are preserved.
lemma η_inv_is_additive (V : FGModuleCat k)
    (f g : Module.Dual k (Module.Dual k V)) :
    η_inv_fun k V (f + g) = η_inv_fun k V f + η_inv_fun k V g := by
  let b := Basis.ofVectorSpace k (↑V)
  simp only [η_inv_fun]
  have h : ∀ i, (f + g) (b.coord i) • b i = f (b.coord i) • b i + g (b.coord i) • b i := by
    intro i
    exact add_smul (f (b.coord i)) (g (b.coord i)) (b i)
  rw [Finset.sum_congr rfl (fun i hi => h i), ← Finset.sum_add_distrib]

-- Verifies that η_inv_fun is a linear map: commutation of scalar multiplication.
lemma η_inv_commutes_scalar_mul (V : FGModuleCat k)
    (a : k) (f : Module.Dual k (Module.Dual k V)) :
    η_inv_fun k V (a • f) = a • η_inv_fun k V f := by
  let b := Basis.ofVectorSpace k (↑V)
  simp only [η_inv_fun]
  have h : ∀ i, (a • f) (b.coord i) • b i = a • f (b.coord i) • b i := by
    intro i
    exact smul_assoc a (f (b.coord i)) (b i)
  rw [Finset.sum_congr rfl (fun i hi => h i), Finset.smul_sum]

-- The inverse of the natural transformation η.
noncomputable def η_inv (V : FGModuleCat k) :
    FGModuleCat.of k (Module.Dual k (Module.Dual k V)) ⟶ V :=
  FGModuleCat.ofHom {
    toFun := η_inv_fun k V,
    map_add' := η_inv_is_additive k V,
    map_smul' := η_inv_commutes_scalar_mul k V,
  }

-- Applying η followed by η_inv gives the identity on V.
lemma η_inv_cancels_η (V : FGModuleCat k) : η k V ≫ η_inv k V = 𝟙 V := by
  ext x
  dsimp [η, η_inv, η_inv_fun]
  exact Basis.sum_repr (Basis.ofVectorSpace k ↑V) x

-- Applying η_inv followed by η gives the identity on the double dual of V.
lemma η_cancels_η_inv(V : FGModuleCat k) :
    η_inv k V ≫ η k V = 𝟙 (FGModuleCat.of k (Module.Dual k (Module.Dual k V))) := by
  ext f g
  dsimp [η, η_inv, η_inv_fun]
  let b := Basis.ofVectorSpace k (↑V)
  calc
    g (∑ i, f (b.coord i) • b i)
      = ∑ i, g (f (b.coord i) • b i) := by simp
    _ = ∑ i, f (b.coord i) • g (b i) := by simp
    _ = ∑ i, g (b i) • f (b.coord i) := by
      apply Finset.sum_congr rfl
      intro i _
      exact mul_comm (f (b.coord i)) (g (b i))
    _ = ∑ i, f (g (b i) • b.coord i) := by simp only [LinearMap.map_smul]
    _ = f (∑ i, g (b i) • b.coord i) := by
      exact Eq.symm (map_sum f (fun x ↦ g (b x) • b.coord x) Finset.univ)
    _ = f g := by rw [Basis.sum_dual_apply_smul_coord b g]


-- The natural isomorphism between the identity functor and the double dual functor.
noncomputable def doubleDualIso : identityFDVec k ≅ doubleDual k := NatIso.ofComponents
    (fun V => {
      hom := η k V,
      inv := η_inv k V,
      hom_inv_id := η_inv_cancels_η k V,
      inv_hom_id := η_cancels_η_inv k V,
    })
    (by
      intros X Y f
      dsimp [doubleDual, η]
      rfl
    )
