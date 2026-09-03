import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoChartCechLaurentChart
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCoverSectional
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_laurentChart_isCompletionAlong_of_powerSeries

universe u v

open CategoryTheory

theorem AlgebraicGeometry.Scheme.TwoAffineOpenCover.exists_laurentChart_isCompletionAlong_of_powerSeries {R : Type u} [CommRing R] {X : AlgebraicGeometry.Scheme.{u}} (𝒱 : X.TwoAffineOpenCover)
    (c : X ⟶ AlgebraicGeometry.Spec (.of R))
    {ι : Type v} (σ : ι → (AlgebraicGeometry.Spec (.of R) ⟶ X)) (h : 𝒱.IsSectional c σ) (i : ι)
    (θ : (𝒱.cover c).A0 →+* PowerSeries R) (hθC : ∀ r : R, θ (algebraMap R (𝒱.cover c).A0 r) = PowerSeries.C r)
    (hθ0 : ∀ (n : ℕ) (a : (𝒱.cover c).A0), (∀ k : ℕ, k < n → PowerSeries.coeff k (θ a) = 0) ↔
      a ∈ RingHom.ker (AlgebraicGeometry.Scheme.TwoAffineOpenCover.sectionAlgHom
        (σ i) (h.comp_eq i) (h.range_subset i)).toRingHom ^ n)
    (hθs : ∀ (n : ℕ) (p : PowerSeries R), ∃ a : (𝒱.cover c).A0, ∀ k : ℕ, k < n →
      PowerSeries.coeff k (θ a) = PowerSeries.coeff k p) :
    ∃ Λ : (𝒱.cover c).LaurentChart,
      (∀ a : (𝒱.cover c).A0, Λ.expand ((𝒱.cover c).ρ0 a) = HahnSeries.ofPowerSeries ℤ R (θ a)) ∧
        Λ.IsCompletionAlong (𝒱.cover c).ρ0
          (AlgebraicGeometry.Scheme.TwoAffineOpenCover.sectionAlgHom (σ i) (h.comp_eq i) (h.range_subset i)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_laurentChart_isCompletionAlong_of_powerSeries.solution
