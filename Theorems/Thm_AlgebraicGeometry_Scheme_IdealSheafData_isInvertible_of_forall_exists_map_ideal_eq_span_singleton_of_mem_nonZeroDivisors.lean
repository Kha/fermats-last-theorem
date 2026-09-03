import Mathlib
import Definitions.Def_AlgebraicCurve_RelCartier
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_IdealSheafData_isInvertible_of_forall_exists_map_ideal_eq_span_singleton_of_mem_nonZeroDivisors

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.IdealSheafData.isInvertible_of_forall_exists_map_ideal_eq_span_singleton_of_mem_nonZeroDivisors
    {X : Scheme.{u}} [IsLocallyNoetherian X] (I : X.IdealSheafData)
    (h : ∀ x : X, ∃ (U : X.affineOpens) (hxU : x ∈ (U : X.Opens)) (g : Γ(X, U)), g ∈ I.ideal U ∧
      (I.ideal U).map (algebraMap Γ(X, U) (Localization.AtPrime (U.2.primeIdealOf ⟨x, hxU⟩).asIdeal)) =
        Ideal.span {algebraMap Γ(X, U) (Localization.AtPrime (U.2.primeIdealOf ⟨x, hxU⟩).asIdeal) g} ∧
      algebraMap Γ(X, U) (Localization.AtPrime (U.2.primeIdealOf ⟨x, hxU⟩).asIdeal) g ∈
        nonZeroDivisors (Localization.AtPrime (U.2.primeIdealOf ⟨x, hxU⟩).asIdeal)) :
    I.IsInvertible := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_isInvertible_of_forall_exists_map_ideal_eq_span_singleton_of_mem_nonZeroDivisors.solution
