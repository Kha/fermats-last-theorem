import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import P2M.Util
import P2M.Sol.S_NeronModelInfra_genericFibreRestrict_injective_of_flat_of_isSeparated

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra

theorem NeronModelInfra.genericFibreRestrict_injective_of_flat_of_isSeparated
    (R : Type u) [CommRing R] [IsDomain R] (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {X T : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) (t : T ⟶ Spec (CommRingCat.of R))
    [IsSeparated f] [Flat t] :
    Function.Injective (genericFibreRestrict R K f t) := by p2m_exact_reverting @_root_.P2MW.S_NeronModelInfra_genericFibreRestrict_injective_of_flat_of_isSeparated.solution
