import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_IdealSheafData_exists_mem_ideal_and_map_eq_span_singleton_and_mem_nonZeroDivisors_of_map_germ_eq_span_singleton

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing

universe u

theorem AlgebraicGeometry.Scheme.IdealSheafData.exists_mem_ideal_and_map_eq_span_singleton_and_mem_nonZeroDivisors_of_map_germ_eq_span_singleton
    {X : Scheme.{u}} (I : X.IdealSheafData) (U : X.affineOpens) (x : ↥X) (hx : x ∈ (U : X.Opens))
    (π : X.presheaf.stalk x) (hgen : (I.ideal U).map (X.presheaf.germ (U : X.Opens) x hx).hom = Ideal.span {π})
    (hπ : π ∈ nonZeroDivisors (X.presheaf.stalk x)) :
    ∃ g : Γ(X, U), g ∈ I.ideal U ∧
      (I.ideal U).map (algebraMap Γ(X, U) (Localization.AtPrime (U.2.primeIdealOf ⟨x, hx⟩).asIdeal)) =
        Ideal.span {algebraMap Γ(X, U) (Localization.AtPrime (U.2.primeIdealOf ⟨x, hx⟩).asIdeal) g} ∧
      algebraMap Γ(X, U) (Localization.AtPrime (U.2.primeIdealOf ⟨x, hx⟩).asIdeal) g ∈
        nonZeroDivisors (Localization.AtPrime (U.2.primeIdealOf ⟨x, hx⟩).asIdeal) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_exists_mem_ideal_and_map_eq_span_singleton_and_mem_nonZeroDivisors_of_map_germ_eq_span_singleton.solution
