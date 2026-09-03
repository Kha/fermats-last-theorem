import Mathlib
import Definitions.Def_DrinfeldCurve_LocalChart
import P2M.Util
import P2M.Sol.S_DrinfeldCurve_LocalChart_smul_drinfeldForm_eq_aeval_linearPart_of_ringHom_semilinear

set_option autoImplicit false

theorem DrinfeldCurve.LocalChart.smul_drinfeldForm_eq_aeval_linearPart_of_ringHom_semilinear
    (q : ℕ) [Fact q.Prime]
    (W : Type) [CommRing W] [IsDomain W] (t : W) (ht : t ≠ 0)
    (f u v : MvPowerSeries (Fin 2) W) (hu : IsUnit u) (hv : IsUnit v)
    (hf : f - DrinfeldCurve.LocalChart.drinfeldForm q W ∈
      (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}) ^ (q + 2))
    (θ : (MvPowerSeries (Fin 2) W ⧸ Ideal.span {MvPowerSeries.C t * v - f * u}) →+*
      (MvPowerSeries (Fin 2) W ⧸ Ideal.span {MvPowerSeries.C t * v - f * u}))
    (σ : W →+* W) (hσ : ∀ w : W, σ w - w ∈ Ideal.span {t}) (w₁ : W) (hw₁ : σ t = t * w₁)
    (hθC : ∀ w : W, θ (Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C t * v - f * u}) (MvPowerSeries.C w)) =
      Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C t * v - f * u}) (MvPowerSeries.C (σ w)))
    (M : Matrix (Fin 2) (Fin 2) W)
    (hM : ∀ jj : Fin 2, θ (Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C t * v - f * u}) (MvPowerSeries.X jj)) -
        Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C t * v - f * u})
          (∑ ii : Fin 2, MvPowerSeries.C (M ii jj) * MvPowerSeries.X ii) ∈
      (Ideal.span {Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C t * v - f * u}) (MvPowerSeries.X 0),
        Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C t * v - f * u}) (MvPowerSeries.X 1)}) ^ 2) :
    Ideal.Quotient.mk (Ideal.span {t}) w₁ •
        (MvPolynomial.X 0 * MvPolynomial.X 1 ^ q - MvPolynomial.X 0 ^ q * MvPolynomial.X 1 :
          MvPolynomial (Fin 2) (W ⧸ Ideal.span {t})) =
      MvPolynomial.aeval
        (fun jj : Fin 2 => ∑ ii : Fin 2,
          MvPolynomial.C (Ideal.Quotient.mk (Ideal.span {t}) (M ii jj)) * MvPolynomial.X ii)
        (MvPolynomial.X 0 * MvPolynomial.X 1 ^ q - MvPolynomial.X 0 ^ q * MvPolynomial.X 1 :
          MvPolynomial (Fin 2) (W ⧸ Ideal.span {t})) := by p2m_exact_reverting @_root_.P2MW.S_DrinfeldCurve_LocalChart_smul_drinfeldForm_eq_aeval_linearPart_of_ringHom_semilinear.solution
