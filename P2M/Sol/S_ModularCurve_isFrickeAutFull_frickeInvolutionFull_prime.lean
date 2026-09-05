module

public import Definitions.Def_ModularCurve_AtkinLehner
public import Theorems.Thm_ModularCurve_exists_isFrickeAutFull
import P2M.Util

@[expose] public section
namespace P2MW.S_ModularCurve_isFrickeAutFull_frickeInvolutionFull_prime

set_option autoImplicit false

open ModularCurve AlgebraicCurve IntermediateField

noncomputable section

theorem solution (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)] : IsFrickeAutFull ℓ (frickeInvolutionFull ℓ) := by
  haveI : NeZero ℓ := ⟨hℓ.out.ne_zero⟩
  exact ModularCurve.isFrickeAutFull_frickeInvolutionFull ℓ (ModularCurve.exists_isFrickeAutFull ℓ)

end
