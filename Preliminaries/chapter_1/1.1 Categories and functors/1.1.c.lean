import Mathlib

open CategoryTheory

universe u v

variable (k : Type u) [Field k] [∀ (V : FGModuleCat k), Module.Finite k V.1]

noncomputable def doubleDual : FGModuleCat k ⥤ FGModuleCat k where
  obj V := FGModuleCat.of k (Module.Dual k (Module.Dual k V))
  map f := FGModuleCat.ofHom (LinearMap.dualMap (LinearMap.dualMap f.hom))

def identityFDVec : FGModuleCat k ⥤ FGModuleCat k where
  obj := id
  map := id

noncomputable def doubleDualEtaHom (V : FGModuleCat k) :
    V ⟶ FGModuleCat.of k (Module.Dual k (Module.Dual k V)) :=
  FGModuleCat.ofHom {
    toFun := fun v => {
      toFun := fun g => g v,
      map_add' := fun g₁ g₂ => by simp,
      map_smul' := fun a g => by simp,
    },
    map_add' := fun v₁ v₂ => by ext; simp,
    map_smul' := fun a v => by ext; simp,
  }

noncomputable def eta_1 (V : FGModuleCat k) (f : Module.Dual k (Module.Dual k V)) : V :=
  let b := Basis.ofVectorSpace k (↑V)
  ∑ i, f (b.coord i) • b i

noncomputable def eta_add (V : FGModuleCat k)
    (f g : Module.Dual k (Module.Dual k V)) :
    eta_1 k V (f + g) = eta_1 k V f + eta_1 k V g := by
  let b := Basis.ofVectorSpace k (↑V)
  simp only [eta_1]
  have h : ∀ i, (f + g) (b.coord i) • b i = f (b.coord i) • b i + g (b.coord i) • b i := by
    intro i
    simp only [LinearMap.add_apply, smul_add]
    exact add_smul (f (b.coord i)) (g (b.coord i)) (b i)
  rw [Finset.sum_congr rfl (fun i hi => h i), ← Finset.sum_add_distrib]

noncomputable def eta_smul (V : FGModuleCat k)
    (a : k) (f : Module.Dual k (Module.Dual k V)) :
    eta_1 k V (a • f) = a • eta_1 k V f := by
  let b := Basis.ofVectorSpace k (↑V)
  simp only [eta_1]
  have h : ∀ i, (a • f) (b.coord i) • b i = a • f (b.coord i) • b i := by
    intro i
    simp only [LinearMap.smul_apply, smul_smul]
    rw [mul_smul]
    exact IsScalarTower.smul_assoc a (f (b.coord i)) (b i)
  rw [Finset.sum_congr rfl (fun i hi => h i), Finset.smul_sum]


noncomputable def doubleDualEtaInvHom (V : FGModuleCat k) :
    FGModuleCat.of k (Module.Dual k (Module.Dual k V)) ⟶ V :=
  FGModuleCat.ofHom {
    toFun := eta_1 k V,
    map_add' := eta_add k V,
    map_smul' := eta_smul k V,
  }

noncomputable def doubleDualEtaIso (V : FGModuleCat k) :
    doubleDualEtaHom k V ≫ doubleDualEtaInvHom k V = 𝟙 V := by
  ext x
  dsimp [doubleDualEtaHom, doubleDualEtaInvHom, eta_1]
  exact Basis.sum_repr (Basis.ofVectorSpace k ↑V) x

omit [∀ (V : FGModuleCat k), Module.Finite k ↑V.obj]

lemma dualFunctionExpansionOnBasis {V : FGModuleCat k}
  (f : Module.Dual k (Module.Dual k ↑V))
  (g : Module.Dual k ↑V)
  (b : Basis (↑(Basis.ofVectorSpaceIndex k ↑V)) k ↑V) :
  g (∑ i, f (b.coord i) • b i) = f g := by
  have g_on_basis : ∑ i, g (b i) • b.coord i = g :=
    Basis.sum_dual_apply_smul_coord b g
  calc
    g (∑ i, f (b.coord i) • b i)
      = ∑ i, g (f (b.coord i) • b i) := by simp
    _ = ∑ i, f (b.coord i) • g (b i) := by simp
    _ = ∑ i, g (b i) • f (b.coord i) := by
      apply Finset.sum_congr rfl
      intro i _
      exact mul_comm (f (b.coord i)) (g (b i))
    _ = ∑ i, f (g (b i) • b.coord i) := by simp only [LinearMap.map_smul]
    _ = f (∑ i, g (b i) • b.coord i) := by exact Eq.symm (map_sum f (fun x ↦ g (b x) • b.coord x) Finset.univ)
    _ = f g := by rw [g_on_basis]

noncomputable def doubleDualEtaIsoInv (V : FGModuleCat k) :
    doubleDualEtaInvHom k V ≫ doubleDualEtaHom k V = 𝟙 (FGModuleCat.of k (Module.Dual k (Module.Dual k V))) := by
  ext f g
  let b := Basis.ofVectorSpace k (↑V)
  have g_on_basis: ∑ i, g (b i) • b.coord i = g := by exact Basis.sum_dual_apply_smul_coord b g
  dsimp [doubleDualEtaHom, doubleDualEtaInvHom, eta_1]
  exact dualFunctionExpansionOnBasis k f g (Basis.ofVectorSpace k ↑V)

noncomputable def doubleDualIso : identityFDVec k ≅ doubleDual k :=
  NatIso.ofComponents
    (fun V => {
      hom := doubleDualEtaHom k V,
      inv := doubleDualEtaInvHom k V,
      hom_inv_id := doubleDualEtaIso k V,
      inv_hom_id := doubleDualEtaIsoInv k V,
    })
    (by
      intros X Y f
      ext v
      dsimp [doubleDual, doubleDualEtaHom]
      rfl
    )
