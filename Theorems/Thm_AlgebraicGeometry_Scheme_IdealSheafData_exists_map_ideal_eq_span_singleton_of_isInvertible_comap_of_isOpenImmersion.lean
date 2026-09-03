import Mathlib
import Definitions.Def_AlgebraicCurve_RelCartier
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_IdealSheafData_exists_map_ideal_eq_span_singleton_of_isInvertible_comap_of_isOpenImmersion

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.IdealSheafData.exists_map_ideal_eq_span_singleton_of_isInvertible_comap_of_isOpenImmersion
    {X Y : Scheme.{u}} (φ : X ⟶ Y) [IsOpenImmersion φ] (J : Y.IdealSheafData)
    (hJ : (J.comap φ).IsInvertible) (x : X) :
    ∃ (U : Y.affineOpens) (hxU : φ.base x ∈ (U : Y.Opens)) (g : Γ(Y, U)), g ∈ J.ideal U ∧
      (J.ideal U).map (algebraMap Γ(Y, U) (Localization.AtPrime (U.2.primeIdealOf ⟨φ.base x, hxU⟩).asIdeal)) =
        Ideal.span {algebraMap Γ(Y, U) (Localization.AtPrime (U.2.primeIdealOf ⟨φ.base x, hxU⟩).asIdeal) g} ∧
      algebraMap Γ(Y, U) (Localization.AtPrime (U.2.primeIdealOf ⟨φ.base x, hxU⟩).asIdeal) g ∈
        nonZeroDivisors (Localization.AtPrime (U.2.primeIdealOf ⟨φ.base x, hxU⟩).asIdeal) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_exists_map_ideal_eq_span_singleton_of_isInvertible_comap_of_isOpenImmersion.solution
