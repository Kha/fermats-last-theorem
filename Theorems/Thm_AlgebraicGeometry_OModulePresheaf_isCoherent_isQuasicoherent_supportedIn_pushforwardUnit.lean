import Mathlib
import Definitions.Def_AlgebraicGeometry_OModulePresheafConstructions
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_isCoherent_isQuasicoherent_supportedIn_pushforwardUnit

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

theorem AlgebraicGeometry.OModulePresheaf.isCoherent_isQuasicoherent_supportedIn_pushforwardUnit
    {R : Type u} [CommRing R] {V Z : Scheme.{u}} (π : V ⟶ Spec (.of R)) (ι : Z ⟶ V) [IsClosedImmersion ι] :
    (OModulePresheaf.pushforwardUnit π ι).IsCoherent ∧ (OModulePresheaf.pushforwardUnit π ι).IsQuasicoherent ∧
      (OModulePresheaf.pushforwardUnit π ι).SupportedIn ⟨Set.range ι.base, ι.isClosedEmbedding.isClosed_range⟩ := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_isCoherent_isQuasicoherent_supportedIn_pushforwardUnit.solution
