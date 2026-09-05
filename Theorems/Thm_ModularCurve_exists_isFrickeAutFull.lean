module

public import Definitions.Def_ModularCurve_AtkinLehner
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_isFrickeAutFull

@[expose] public section

open ModularCurve AlgebraicCurve IntermediateField
theorem ModularCurve.exists_isFrickeAutFull (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)] : ∃ σ : modularFunctionFieldFull ℓ ≃ₐ[ℚ] modularFunctionFieldFull ℓ, IsFrickeAutFull ℓ σ := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_isFrickeAutFull.solution
