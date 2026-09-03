import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.Algebra.Support
import P2M.Util
import P2M.Sol.S_DixmierMalliavin_exists_contDiff_tendsto_integral_mul

set_option autoImplicit false

theorem DixmierMalliavin.exists_contDiff_tendsto_integral_mul (δ : ℝ) (hδ : 0 < δ) :
    ∃ thr : (N : ℕ) → (Fin N → ℝ) → ℝ, (∀ N p, 0 < thr N p) ∧
      ∀ a : ℕ → ℝ, (∀ N, 0 < a N ∧ a N ≤ thr N (fun i : Fin N => a i)) →
        ∃ φ ψ : ℝ → ℂ, ContDiff ℝ (⊤ : ℕ∞) φ ∧ ContDiff ℝ (⊤ : ℕ∞) ψ ∧
          tsupport φ ⊆ Set.Icc (-δ) δ ∧ tsupport ψ ⊆ Set.Icc (-δ) δ ∧
          ∀ F : ℝ → ℂ, ContDiff ℝ (⊤ : ℕ∞) F → ∀ P : ℕ → ℝ → ℂ, P 0 = F →
            (∀ N, P (N + 1) = fun t => P N t - (((a N) ^ 2 : ℝ) : ℂ) * deriv (deriv (P N)) t) →
              Filter.Tendsto (fun N : ℕ => ∫ t, φ t * P N t) Filter.atTop
                (nhds (F 0 + ∫ t, ψ t * F t)) := by p2m_exact_reverting @_root_.P2MW.S_DixmierMalliavin_exists_contDiff_tendsto_integral_mul.solution
