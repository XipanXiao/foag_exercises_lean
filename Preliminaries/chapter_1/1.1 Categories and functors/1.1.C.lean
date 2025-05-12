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

noncomputable def doubleDualIso : identityFDVec k ≅ doubleDual k :=
  NatIso.ofComponents
    (fun V =>
      { hom := FGModuleCat.ofHom (Module.evalEquiv k V).toLinearMap
        inv := FGModuleCat.ofHom (Module.evalEquiv k V).symm.toLinearMap
        hom_inv_id := by ext; apply (Module.evalEquiv k V).symm_apply_apply
        inv_hom_id := by ext; apply (Module.evalEquiv k V).apply_symm_apply })
    (by intros X Y f; ext; rfl)
