import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import Definitions.Def_SheafOfModules_MonoidalV2
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_AffHom_nonempty_H0_equiv_and_HSucc_equiv_of_bijective
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_tensorUnit_unit

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry"

noncomputable section

namespace AC2Aux

variable {R : Type u} [CommRing R] {V : Scheme.{u}} (π : V ⟶ Spec (CommRingCat.of R))

def appU (U : V.affineOpens) :
    (OModulePresheaf.ofModules π (𝟙_ (V.Modules))).obj U.1 →ₗ[R] (OModulePresheaf.unit π).obj U.1 :=
  { toFun := fun x => (x : (OModulePresheaf.unit π).obj U.1)
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }

theorem appU_bijective (U : V.affineOpens) : Function.Bijective (appU π U) :=
  ⟨fun _ _ h => h, fun y => ⟨y, rfl⟩⟩

def hom : OModulePresheaf.AffHom (OModulePresheaf.ofModules π (𝟙_ (V.Modules))) (OModulePresheaf.unit π) where
  app := appU π
  app_smul := fun _ _ _ => rfl
  naturality := fun _ => rfl

end AC2Aux

end

open AC2Aux in
theorem solution
    {R : Type u} [CommRing R] {V : Scheme.{u}} (π : V ⟶ Spec (CommRingCat.of R)) [IsSeparated π]
    (K : V.OrderedAffineCover) :
    Nonempty ((OModulePresheaf.ofModules π (𝟙_ (V.Modules))).H0 K ≃ₗ[R] (OModulePresheaf.unit π).H0 K) ∧
      ∀ i : ℕ, Nonempty ((OModulePresheaf.ofModules π (𝟙_ (V.Modules))).HSucc K i ≃ₗ[R] (OModulePresheaf.unit π).HSucc K i) := by
  exact AlgebraicGeometry.OModulePresheaf.AffHom.nonempty_H0_equiv_and_HSucc_equiv_of_bijective (hom π) (appU_bijective π) K
