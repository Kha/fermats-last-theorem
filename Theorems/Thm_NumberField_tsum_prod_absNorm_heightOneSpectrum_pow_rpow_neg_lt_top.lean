import Mathlib.NumberTheory.NumberField.Ideal.Asymptotics
import P2M.Util
import P2M.Sol.S_NumberField_tsum_prod_absNorm_heightOneSpectrum_pow_rpow_neg_lt_top

open NumberField IsDedekindDomain
open scoped ENNReal

theorem NumberField.tsum_prod_absNorm_heightOneSpectrum_pow_rpow_neg_lt_top
    (F : Type) [Field F] [NumberField F] {t : ℝ} (ht : 1 < t) :
    ∑' k : HeightOneSpectrum (𝓞 F) →₀ ℕ,
        (((k.prod fun v n => Ideal.absNorm v.asIdeal ^ n : ℕ) : ℝ≥0∞) ^ (-t)) < ⊤ := by p2m_exact_reverting @_root_.P2MW.S_NumberField_tsum_prod_absNorm_heightOneSpectrum_pow_rpow_neg_lt_top.solution
