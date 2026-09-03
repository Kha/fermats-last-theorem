import Mathlib
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_toDescentData_map_bijective_of_openCover
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_toDescentData_essSurj_of_openCover
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_isStackFor_openCover

set_option autoImplicit false

universe v u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem solution (Y : Scheme.{u}) (𝒰 : Y.OpenCover) :
    ((Scheme.Modules.pseudofunctor.{u}).comp Bicategory.Adj.forget₁).IsStackFor
      (Presieve.ofArrows 𝒰.X 𝒰.f) := by
  rw [Pseudofunctor.isStackFor_ofArrows_iff]
  set F := ((Scheme.Modules.pseudofunctor.{u}).comp Bicategory.Adj.forget₁).toDescentData 𝒰.f with hF
  have hcov : ∀ y : Y, ∃ i, y ∈ Set.range (𝒰.f i).base := fun y => ⟨𝒰.idx y, 𝒰.covers y⟩
  haveI : F.Faithful :=
    ⟨fun {L₁ L₂} => (Scheme.Modules.toDescentData_map_bijective_of_openCover 𝒰.f hcov L₁ L₂).1⟩
  haveI : F.Full :=
    ⟨fun {L₁ L₂} φ => ⟨_, ((Scheme.Modules.toDescentData_map_bijective_of_openCover 𝒰.f hcov L₁ L₂).2 φ).choose_spec⟩⟩
  haveI : F.EssSurj := Scheme.Modules.toDescentData_essSurj_of_openCover 𝒰.f hcov
  exact { faithful := inferInstance, full := inferInstance, essSurj := inferInstance }
