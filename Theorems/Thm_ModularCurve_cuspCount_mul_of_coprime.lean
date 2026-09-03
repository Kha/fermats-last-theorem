import Definitions.Def_ModularCurve_GenusNumerics
import P2M.Util
import P2M.Sol.S_ModularCurve_cuspCount_mul_of_coprime

open ModularCurve
theorem ModularCurve.cuspCount_mul_of_coprime {M N : ℕ} (hM : M ≠ 0) (hN : N ≠ 0) (hMN : Nat.Coprime M N) : cuspCount (M * N) = cuspCount M * cuspCount N := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_cuspCount_mul_of_coprime.solution
