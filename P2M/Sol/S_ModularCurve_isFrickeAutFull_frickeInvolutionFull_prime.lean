module

public import Definitions.Def_ModularCurve_AtkinLehner
import P2M.Sol.S_ModularCurve_exists_isFrickeAutFull
import P2M.Util

namespace P2MW.S_ModularCurve_isFrickeAutFull_frickeInvolutionFull_prime

set_option autoImplicit false

open ModularCurve AlgebraicCurve IntermediateField

noncomputable section

theorem solution (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)] : IsFrickeAutFull ℓ (frickeInvolutionFull ℓ) := by
  haveI : NeZero ℓ := ⟨hℓ.out.ne_zero⟩
  exact ModularCurve.isFrickeAutFull_frickeInvolutionFull ℓ (ModularCurve.exists_isFrickeAutFull ℓ)

end
end S_ModularCurve_isFrickeAutFull_frickeInvolutionFull_prime
end P2MW

public section
open ModularCurve AlgebraicCurve IntermediateField
theorem ModularCurve.isFrickeAutFull_frickeInvolutionFull_prime (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)] : IsFrickeAutFull ℓ (frickeInvolutionFull ℓ) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_isFrickeAutFull_frickeInvolutionFull_prime.solution
end
