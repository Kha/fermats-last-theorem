import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_exists_etale_nhd_of_flat_stalkMap_of_map_maximalIdeal_eq_of_isIso_residueFieldMap

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.exists_etale_nhd_of_flat_stalkMap_of_map_maximalIdeal_eq_of_isIso_residueFieldMap
    {U S : Scheme.{u}} (f : U ⟶ S) [LocallyOfFinitePresentation f] (x : U)
    (hflat : (f.stalkMap x).hom.Flat)
    (hmax : Ideal.map (f.stalkMap x).hom (IsLocalRing.maximalIdeal (S.presheaf.stalk (f x))) =
      IsLocalRing.maximalIdeal (U.presheaf.stalk x))
    [IsIso (f.residueFieldMap x)] :
    ∃ V : U.Opens, x ∈ V ∧ Etale (V.ι ≫ f) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_etale_nhd_of_flat_stalkMap_of_map_maximalIdeal_eq_of_isIso_residueFieldMap.solution
