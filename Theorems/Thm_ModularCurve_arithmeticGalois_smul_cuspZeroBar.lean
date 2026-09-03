import Definitions.Def_ModularCurve_CuspidalClass
import P2M.Util
import P2M.Sol.S_ModularCurve_arithmeticGalois_smul_cuspZeroBar

open ModularCurve AlgebraicCurve

theorem ModularCurve.arithmeticGalois_smul_cuspZeroBar (N : ℕ) [NeZero N] (τ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)) : arithmeticGalois (modularFunctionFieldFull N) τ • cuspZeroBar N = cuspZeroBar N := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_arithmeticGalois_smul_cuspZeroBar.solution
