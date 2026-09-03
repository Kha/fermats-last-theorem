import Mathlib
import Definitions.Def_DrinfeldCurve_LocalChart
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import P2M.Util
import P2M.Sol.S_FormalGroup_IsDrinfeldBasisAdic_exists_mem_pow_isUnit_homogeneous_of_coeff_nthSeries_of_ringEquiv_drinfeldChart

set_option autoImplicit false

open IsLocalRing FormalGroup

theorem FormalGroup.IsDrinfeldBasisAdic.exists_mem_pow_isUnit_homogeneous_of_coeff_nthSeries_of_ringEquiv_drinfeldChart
    (q : ℕ) [Fact q.Prime]
    (R : Type) [CommRing R] [IsLocalRing R]
    (F : FormalGroup R)
    (x₀ x₁ : R) (hD : F.IsDrinfeldBasisAdic (maximalIdeal R) q x₀ x₁)

    (T : R) (hT : ∃ w : R, IsUnit w ∧ PowerSeries.coeff q (F.nthSeries q) - w * T ∈ Ideal.span {(q : R)})

    (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (maximalIdeal W) W]
    (π : W) (hπ : maximalIdeal W = Ideal.span {π}) (ε : W) (hε : IsUnit ε) (hπq : π ^ (q - 1) = ε * (q : W))
    (f u v : MvPowerSeries (Fin 2) W) (hu : IsUnit u) (hv : IsUnit v)
    (hf : f - DrinfeldCurve.LocalChart.drinfeldForm q W ∈
      (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}) ^ (q + 2))
    (e : R ≃+* MvPowerSeries (Fin 2) W ⧸ Ideal.span {MvPowerSeries.C π * v - f * u})
    (he₀ : e x₀ = Ideal.Quotient.mk _ (MvPowerSeries.X 0)) (he₁ : e x₁ = Ideal.Quotient.mk _ (MvPowerSeries.X 1)) :
    ∃ (h : MvPowerSeries (Fin 2) W)
      (_ : h ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}) ^ (q * (q - 1))),
      (∀ a b : W, (a ∉ maximalIdeal W ∨ b ∉ maximalIdeal W) →
          a ^ q * b - a * b ^ q ∈ maximalIdeal W →
          IsUnit (∑ i ∈ Finset.range (q * (q - 1) + 1),
            MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) i + Finsupp.single (1 : Fin 2) (q * (q - 1) - i)) h
              * a ^ i * b ^ (q * (q - 1) - i))) ∧
      e T = Ideal.Quotient.mk _ h := by p2m_exact_reverting @_root_.P2MW.S_FormalGroup_IsDrinfeldBasisAdic_exists_mem_pow_isUnit_homogeneous_of_coeff_nthSeries_of_ringEquiv_drinfeldChart.solution
