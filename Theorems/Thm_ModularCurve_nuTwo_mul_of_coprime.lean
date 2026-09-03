import Definitions.Def_ModularCurve_GenusNumerics
import P2M.Util
import P2M.Sol.S_ModularCurve_nuTwo_mul_of_coprime

open ModularCurve
theorem ModularCurve.nuTwo_mul_of_coprime {M N : ℕ} (h : Nat.Coprime M N) : nuTwo (M * N) = nuTwo M * nuTwo N := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_nuTwo_mul_of_coprime.solution
