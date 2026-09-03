import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import P2M.Util
import P2M.Sol.S_NeronModelInfra_neronUniqueExtension_of_forall_quasiCompact

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra

theorem NeronModelInfra.neronUniqueExtension_of_forall_quasiCompact
    (R : Type u) [CommRing R] [IsDomain R] (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [IsSeparated f]
    (h : ∀ (T : Scheme.{u}) (t : T ⟶ Spec (CommRingCat.of R)), Smooth t → QuasiCompact t →
      Function.Bijective (genericFibreRestrict R K f t)) :
    NeronUniqueExtension R K f := by p2m_exact_reverting @_root_.P2MW.S_NeronModelInfra_neronUniqueExtension_of_forall_quasiCompact.solution
