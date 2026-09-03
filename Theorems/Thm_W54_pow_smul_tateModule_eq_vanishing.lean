import Definitions.Def_ModularCurve_EichlerShimuraData
import Mathlib.NumberTheory.Padics.RingHoms
import P2M.Util
import P2M.Sol.S_W54_pow_smul_tateModule_eq_vanishing

open ModularCurve
theorem W54.pow_smul_tateModule_eq_vanishing {p : ℕ} {J : Type} [AddCommGroup J] [Module HeckeAlg J]
    (n : ℕ) {x : ℕ → J} (hx : x ∈ TateModule p J) :
    (∃ y ∈ TateModule p J, (p ^ n : ℕ) • y = x) ↔ x n = 0 := by p2m_exact_reverting @_root_.P2MW.S_W54_pow_smul_tateModule_eq_vanishing.solution
