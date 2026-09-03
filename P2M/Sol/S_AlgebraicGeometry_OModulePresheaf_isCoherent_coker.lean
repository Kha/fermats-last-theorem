import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.Localization.Away.Basic
import Definitions.Def_AlgebraicGeometry_OModulePresheafConstructions
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_isCoherent_coker

set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option autoImplicit false

p2m_open "AlgebraicGeometry P2MW.S_AlgebraicGeometry_OModulePresheaf_isCoherent_coker.AlgebraicGeometry CategoryTheory TopologicalSpace Opposite"

noncomputable section

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec Scheme OModulePresheaf.coker OModulePresheaf.imCokerSES OModulePresheaf.Hom OModulePresheaf OModulePresheaf.IsCoherent"
namespace OModulePresheaf
p2m_export "AlgebraicGeometry.OModulePresheaf" "coker imCokerSES Hom IsCoherent"
namespace G4T
p2m_open "AlgebraicGeometry.OModulePresheaf AlgebraicGeometry"

universe u

section PModAlg
variable {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)}
variable {F G : OModulePresheaf π} (φ : OModulePresheaf.Hom F G)

theorem isCoherent_coker (hG : OModulePresheaf.IsCoherent G) :
    OModulePresheaf.IsCoherent (OModulePresheaf.coker φ) := fun U => by
  haveI := hG U
  exact Module.Finite.of_surjective ((OModulePresheaf.imCokerSES φ).proj.appSections U.1)
    ((OModulePresheaf.imCokerSES φ).surjective U.1)

end PModAlg

end AlgebraicGeometry.OModulePresheaf.G4T

end

universe u

open _root_.AlgebraicGeometry _root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_isCoherent_coker.AlgebraicGeometry in
theorem solution {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)} {F G : OModulePresheaf π} (φ : OModulePresheaf.Hom F G) (hG : G.IsCoherent) : (OModulePresheaf.coker φ).IsCoherent :=
  AlgebraicGeometry.OModulePresheaf.G4T.isCoherent_coker φ hG
