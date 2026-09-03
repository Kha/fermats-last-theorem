import Definitions.Def_ModularCurve_GenusNumerics
import P2M.Util
import P2M.Sol.S_ModularCurve_nuThree_mul_of_coprime

open ModularCurve
theorem ModularCurve.nuThree_mul_of_coprime {M N : ℕ} (h : Nat.Coprime M N) : nuThree (M * N) = nuThree M * nuThree N := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_nuThree_mul_of_coprime.solution
