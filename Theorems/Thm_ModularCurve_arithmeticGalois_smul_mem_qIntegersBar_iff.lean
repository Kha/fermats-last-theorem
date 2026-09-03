import Definitions.Def_ModularCurve_AtkinLehner
import P2M.Util
import P2M.Sol.S_ModularCurve_arithmeticGalois_smul_mem_qIntegersBar_iff

open ModularCurve AlgebraicCurve

theorem ModularCurve.arithmeticGalois_smul_mem_qIntegersBar_iff (N : ℕ) (τ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)) (x : modularFunctionFieldBar N) : arithmeticGalois (modularFunctionFieldFull N) τ • x ∈ qIntegersBar (AlgebraicClosure ℚ) (modularFunctionFieldBar N) ↔ x ∈ qIntegersBar (AlgebraicClosure ℚ) (modularFunctionFieldBar N) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_arithmeticGalois_smul_mem_qIntegersBar_iff.solution
