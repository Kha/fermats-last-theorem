import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_exists_section_of_flat_of_locallyQuasiFinite_of_henselianLocalRing_of_isAlgClosed

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry~exists_isFinite_isOpenImmersion_isClosed_cover_isEmpty_pullback_of_locallyQuasiFinite_of_henselianLocalRing~exists_section_comp_eq_iff_factors_of_universallyClosed_of_valuationRing"

theorem AlgebraicGeometry.exists_section_of_flat_of_locallyQuasiFinite_of_henselianLocalRing_of_isAlgClosed
    (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R] [HenselianLocalRing R]
    (K : Type u) [Field K] [IsAlgClosed K] [Algebra R K] [IsFractionRing R K]
    {X : Scheme.{u}} (g : X ⟶ Spec (.of R))
    [LocallyOfFiniteType g] [LocallyQuasiFinite g] [IsSeparated g] [QuasiCompact g] [Flat g]
    (x : X) (hx : g.base x = IsLocalRing.closedPoint R) :
    ∃ s : Spec (.of R) ⟶ X, s ≫ g = 𝟙 _ := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_section_of_flat_of_locallyQuasiFinite_of_henselianLocalRing_of_isAlgClosed.solution
