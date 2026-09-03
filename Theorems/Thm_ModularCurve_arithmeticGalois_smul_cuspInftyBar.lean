import Definitions.Def_ModularCurve_AtkinLehner
import P2M.Util
import P2M.Sol.S_ModularCurve_arithmeticGalois_smul_cuspInftyBar

open ModularCurve AlgebraicCurve

theorem ModularCurve.arithmeticGalois_smul_cuspInftyBar (N : ℕ) [NeZero N] (τ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)) : arithmeticGalois (modularFunctionFieldFull N) τ • cuspInftyBar N = cuspInftyBar N := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_arithmeticGalois_smul_cuspInftyBar.solution
