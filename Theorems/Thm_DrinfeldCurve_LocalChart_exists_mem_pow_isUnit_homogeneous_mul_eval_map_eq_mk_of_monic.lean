import Mathlib
import Definitions.Def_DrinfeldCurve_LocalChart
import P2M.Util
import P2M.Sol.S_DrinfeldCurve_LocalChart_exists_mem_pow_isUnit_homogeneous_mul_eval_map_eq_mk_of_monic

set_option autoImplicit false

open IsLocalRing

theorem DrinfeldCurve.LocalChart.exists_mem_pow_isUnit_homogeneous_mul_eval_map_eq_mk_of_monic
    (q : ℕ) [Fact q.Prime] (W : Type) [CommRing W] [IsLocalRing W]
    (π : W) (hπ : maximalIdeal W = Ideal.span {π})
    (f u v : MvPowerSeries (Fin 2) W) (hv : IsUnit v)
    (hf : f - DrinfeldCurve.LocalChart.drinfeldForm q W ∈
      (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}) ^ (q + 2))
    (s : MvPowerSeries (Fin 2) W ⧸ Ideal.span {MvPowerSeries.C π * v - f * u}) (hs : IsUnit s)
    (d k : ℕ) (h : MvPowerSeries (Fin 2) W)
    (hh : h ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}) ^ d)
    (hunit : ∀ a b : W, (a ∉ maximalIdeal W ∨ b ∉ maximalIdeal W) →
        a ^ q * b - a * b ^ q ∈ maximalIdeal W →
        IsUnit (∑ i ∈ Finset.range (d + 1),
            MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) i + Finsupp.single (1 : Fin 2) (d - i)) h
              * a ^ i * b ^ (d - i)))
    (P : Polynomial W) (hPm : P.Monic) (hPk : P.natDegree = k)
    (hPc : ∀ i < k, P.coeff i ∈ maximalIdeal W ^ (((k - i) * d) / (q + 1) + 1)) :
    ∃ (h' : MvPowerSeries (Fin 2) W)
      (_ : h' ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}) ^ (d * k)),
      (∀ a b : W, (a ∉ maximalIdeal W ∨ b ∉ maximalIdeal W) →
          a ^ q * b - a * b ^ q ∈ maximalIdeal W →
          IsUnit (∑ i ∈ Finset.range (d * k + 1),
            MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) i + Finsupp.single (1 : Fin 2) (d * k - i)) h'
              * a ^ i * b ^ (d * k - i))) ∧
      s * (P.map ((Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C π * v - f * u})).comp
            (MvPowerSeries.C : W →+* MvPowerSeries (Fin 2) W))).eval
          (Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C π * v - f * u}) h) =
        Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C π * v - f * u}) h' := by p2m_exact_reverting @_root_.P2MW.S_DrinfeldCurve_LocalChart_exists_mem_pow_isUnit_homogeneous_mul_eval_map_eq_mk_of_monic.solution
