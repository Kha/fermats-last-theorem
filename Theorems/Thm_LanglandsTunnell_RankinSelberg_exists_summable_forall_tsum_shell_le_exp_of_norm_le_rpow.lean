import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_HaarQuotient
import Definitions.Def_AutomorphicForm_ConstantTerm
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_RankinSelberg_exists_summable_forall_tsum_shell_le_exp_of_norm_le_rpow

set_option autoImplicit false

attribute [local instance] NumberField.AdelicHaar.glBorel

p2m_open "MeasureTheory NumberField~summable_heightOneSpectrum_tsum_pow_mul_absNorm_rpow_neg_rat AutomorphicForm IsDedekindDomain UnramifiedWhittaker~norm_heckeRecursionSeq_le_mul_pow_of_norm_le_rpow"
open LanglandsTunnell.RankinSelberg

theorem LanglandsTunnell.RankinSelberg.exists_summable_forall_tsum_shell_le_exp_of_norm_le_rpow
    (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (lam om lam' om' : HeightOneSpectrum (𝓞 ℚ) → ℂ) (κ : ℝ)
    (hbd : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S →
      ‖lam v‖ ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ κ ∧ ‖om v‖ ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ κ ∧
      ‖lam' v‖ ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ κ ∧ ‖om' v‖ ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ κ)
    (τ : ℝ) (hτ : 2 * |κ| + 4 < τ) :
    ∃ b : {v : HeightOneSpectrum (𝓞 ℚ) // v ∉ S} → ℝ, (∀ v, 0 ≤ b v) ∧ Summable b ∧
      ∀ v : {v : HeightOneSpectrum (𝓞 ℚ) // v ∉ S},
        (∑' p : ℤ × ℤ,
            ENNReal.ofReal
              (((Ideal.absNorm v.1.asIdeal : ℕ) : ℝ) ^ (p.1 - p.2) *
                ‖(if 0 ≤ p.1 - p.2 ∧ 0 ≤ p.2 then
                    (om v.1 * om' v.1) ^ p.2.toNat *
                      heckeRecursionSeq ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) (lam v.1) (om v.1) (p.1 - p.2).toNat *
                      heckeRecursionSeq ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) (lam' v.1) (om' v.1) (p.1 - p.2).toNat
                  else 0)‖ *
                (((Ideal.absNorm v.1.asIdeal : ℕ) : ℝ) ^ (-(p.1 + p.2))) ^ τ)) ≤ ENNReal.ofReal (Real.exp (b v)) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_RankinSelberg_exists_summable_forall_tsum_shell_le_exp_of_norm_le_rpow.solution
