import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Definitions.Def_EisensteinGeneral_LocalCorrection
import P2M.Util
import P2M.Sol.S_EisensteinGeneral_LocalCorrection_norm_corrOff_le_of_le_re

set_option autoImplicit false

open EisensteinGeneral.LocalCorrection

theorem EisensteinGeneral.LocalCorrection.norm_corrOff_le_of_le_re
    {χϖ : ℂ} (hχ : ‖χϖ‖ = 1) {N : ℕ} (hN : 2 ≤ N) (e : ℤ) {σ₁ : ℝ} (k' : ℕ)
    (hk' : 2 * max 0 (-σ₁) ≤ k') {s : ℂ} (hs : σ₁ ≤ s.re) :
    ‖corrOff χϖ N e s‖ ≤ ((N : ℝ) ^ (-e).toNat) ^ (k' + 1) := by p2m_exact_reverting @_root_.P2MW.S_EisensteinGeneral_LocalCorrection_norm_corrOff_le_of_le_re.solution
