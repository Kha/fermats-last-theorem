import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.Localization.Away.Basic
import Definitions.Def_AlgebraicGeometry_OModulePresheafIdealFiltration
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_isCoherent_idealPowQuot

set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option autoImplicit false

p2m_open "AlgebraicGeometry P2MW.S_AlgebraicGeometry_OModulePresheaf_isCoherent_idealPowQuot.AlgebraicGeometry CategoryTheory TopologicalSpace Opposite"

noncomputable section

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "IsLocallyNoetherian Spec Scheme IsLocallyNoetherian.component_noetherian IsNoetherian OModulePresheaf.idealPowQuot OModulePresheaf OModulePresheaf.IsCoherent Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.algebraOfHom"
namespace OModulePresheaf
p2m_export "AlgebraicGeometry.OModulePresheaf" "idealPowSub idealPow idealPowSuccSub idealPowQuot_smul_mk idealPowQuot IsCoherent isScalarTower obj"
namespace G4T
p2m_open "AlgebraicGeometry.OModulePresheaf AlgebraicGeometry"

universe u

section Closure

variable {R : Type u} [CommRing R] {V : Scheme.{u}} (π : V ⟶ Spec (.of R))

theorem isCoherent_idealPowQuot [IsLocallyNoetherian V] (I : V.IdealSheafData)
    (F : OModulePresheaf π) (k : ℕ) (hFc : OModulePresheaf.IsCoherent F) :
    OModulePresheaf.IsCoherent (idealPowQuot π I F k) := fun U => by
  letI := (Scheme.TwoAffineOpenCover.algebraOfHom π U.1).toModule; haveI := F.isScalarTower U.1
  haveI := IsLocallyNoetherian.component_noetherian U
  haveI := hFc U
  haveI : _root_.IsNoetherian (Γ(V, U.1)) (F.obj U.1) := isNoetherian_of_isNoetherianRing_of_finite _ _
  let mkΓ : (idealPow π I F k).obj U.1
      →ₗ[Γ(V, U.1)] (idealPowQuot π I F k).obj U.1 :=
    { toFun := (idealPowSuccSub π I F k U.1).mkQ
      map_add' := map_add _
      map_smul' := fun a y => (idealPowQuot_smul_mk π I F k U.1 a y).symm }
  haveI : Module.Finite Γ(V, U.1) ((idealPow π I F k).obj U.1) :=
    Module.Finite.of_injective
      ({ toFun := (idealPowSub π I F k U.1).subtype
         map_add' := map_add _
         map_smul' := fun a y => rfl } :
        (idealPow π I F k).obj U.1 →ₗ[Γ(V, U.1)] F.obj U.1)
      Subtype.val_injective
  exact Module.Finite.of_surjective mkΓ (Submodule.mkQ_surjective _)

end Closure

end AlgebraicGeometry.OModulePresheaf.G4T

end

universe u

open _root_.AlgebraicGeometry _root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_isCoherent_idealPowQuot.AlgebraicGeometry in
theorem solution {R : Type u} [CommRing R] {V : Scheme.{u}} (π : V ⟶ Spec (.of R)) [IsLocallyNoetherian V] (I : V.IdealSheafData) (F : OModulePresheaf π) (k : ℕ) (hFc : F.IsCoherent) : (OModulePresheaf.idealPowQuot π I F k).IsCoherent :=
  AlgebraicGeometry.OModulePresheaf.G4T.isCoherent_idealPowQuot π I F k hFc
