import Mathlib
import P2M.Util
import P2M.Sol.S_ModularCurve_SiegelUnit_mem_span_levelBernoulliWeight_dilate_iff_even

set_option autoImplicit false

theorem ModularCurve.SiegelUnit.mem_span_levelBernoulliWeight_dilate_iff_even (N : ℕ) [NeZero N]
    (φ : ZMod N → ℚ) :
    φ ∈ Submodule.span ℚ (Set.range fun s : ZMod N => fun r : ZMod N =>
        ((6 * (((s * r).val : ℕ) : ℤ) ^ 2 - 6 * (N : ℤ) * (((s * r).val : ℕ) : ℤ) + (N : ℤ) ^ 2 : ℤ) : ℚ)) ↔
      ∀ r : ZMod N, φ (-r) = φ r := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_SiegelUnit_mem_span_levelBernoulliWeight_dilate_iff_even.solution
