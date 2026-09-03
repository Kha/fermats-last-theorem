import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoChartCechLaurentChart
import P2M.Util
import P2M.Sol.S_RingHom_laurentSeries_derivative_eq_of_kaehlerDifferential_D_eq_smul

universe u v

theorem RingHom.laurentSeries_derivative_eq_of_kaehlerDifferential_D_eq_smul {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
    (Λ : A →+* LaurentSeries R) (hΛC : ∀ r : R, Λ (algebraMap R A r) = HahnSeries.C r)
    {t₀ : A} (ht₀ : Λ t₀ = HahnSeries.single 1 1) :
    (∀ g c : A, KaehlerDifferential.D R A g = c • KaehlerDifferential.D R A t₀ →
        LaurentSeries.derivative R (Λ g) = Λ c) ∧
      (Nontrivial R → KaehlerDifferential.D R A t₀ ≠ 0) := by p2m_exact_reverting @_root_.P2MW.S_RingHom_laurentSeries_derivative_eq_of_kaehlerDifferential_D_eq_smul.solution
