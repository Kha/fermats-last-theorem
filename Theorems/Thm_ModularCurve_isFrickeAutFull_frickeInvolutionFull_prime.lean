module

public import Definitions.Def_ModularCurve_AtkinLehner
import P2M.Util
import P2M.Sol.S_ModularCurve_isFrickeAutFull_frickeInvolutionFull_prime

@[expose] public section

open ModularCurve AlgebraicCurve IntermediateField
theorem ModularCurve.isFrickeAutFull_frickeInvolutionFull_prime (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)] : IsFrickeAutFull ℓ (frickeInvolutionFull ℓ) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_isFrickeAutFull_frickeInvolutionFull_prime.solution
