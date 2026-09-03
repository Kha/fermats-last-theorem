import Mathlib.Analysis.Complex.Basic
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_RankinSelberg_exists_multipliable_differentiableOn_tprod_inv_eval_rsEulerPoly_of_norm_le_rpow

set_option autoImplicit false

p2m_open "IsDedekindDomain NumberField~multipliable_differentiableOn_tprod_ne_zero_eulerProduct_of_norm_le_one"

theorem LanglandsTunnell.RankinSelberg.exists_multipliable_differentiableOn_tprod_inv_eval_rsEulerPoly_of_norm_le_rpow
    (K : Type) [Field K] [NumberField K] (S : Finset (HeightOneSpectrum (𝓞 K)))
    (a b a' b' : {v : HeightOneSpectrum (𝓞 K) // v ∉ S} → ℂ) (κ : ℝ)
    (hbd : ∀ v, ‖a v‖ ≤ ((Ideal.absNorm v.1.asIdeal : ℕ) : ℝ) ^ κ ∧ ‖b v‖ ≤ ((Ideal.absNorm v.1.asIdeal : ℕ) : ℝ) ^ κ ∧
      ‖a' v‖ ≤ ((Ideal.absNorm v.1.asIdeal : ℕ) : ℝ) ^ κ ∧ ‖b' v‖ ≤ ((Ideal.absNorm v.1.asIdeal : ℕ) : ℝ) ^ κ) :
    ∃ σ₀ : ℝ,
      (∀ s : ℂ, σ₀ < s.re →
        Multipliable (fun v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S} =>
          ((LanglandsTunnell.RankinSelberg.rsEulerPoly (a v) (b v) (a' v) (b' v) 0).eval
            (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹)) ∧
      DifferentiableOn ℂ (fun s : ℂ => ∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S},
          ((LanglandsTunnell.RankinSelberg.rsEulerPoly (a v) (b v) (a' v) (b' v) 0).eval
            (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹) {s : ℂ | σ₀ < s.re} ∧
      (∀ s : ℂ, σ₀ < s.re →
        (∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S},
          ((LanglandsTunnell.RankinSelberg.rsEulerPoly (a v) (b v) (a' v) (b' v) 0).eval
            (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹) ≠ 0) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_RankinSelberg_exists_multipliable_differentiableOn_tprod_inv_eval_rsEulerPoly_of_norm_le_rpow.solution
