import Mathlib
import Definitions.Def_ModularCurve_GenusNumerics
import P2M.Util
import P2M.Sol.S_ModularCurve_genusFormula_isNat

theorem ModularCurve.genusFormula_isNat {N : ℕ} (hN : 0 < N) : ∃ g : ℕ, (g : ℚ) = ModularCurve.genusFormula N := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_genusFormula_isNat.solution
