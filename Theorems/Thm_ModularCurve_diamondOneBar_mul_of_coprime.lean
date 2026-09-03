import Mathlib
import Definitions.Def_ModularCurve_X1HeckeModule
import P2M.Util
import P2M.Sol.S_ModularCurve_diamondOneBar_mul_of_coprime

set_option autoImplicit false

theorem ModularCurve.diamondOneBar_mul_of_coprime (M : ℕ) [NeZero M]
    (hdia : ∀ d : ℕ, Nat.Coprime d M →
      (∃ σ₀ : ModularCurve.x1FunctionField M ≃ₐ[ℚ] ModularCurve.x1FunctionField M,
          ModularCurve.IsDiamondAut M d σ₀) ∧
        ∃ σ' : ModularCurve.x1FunctionFieldBar M ≃ₐ[AlgebraicClosure ℚ]
            ModularCurve.x1FunctionFieldBar M,
          ModularCurve.IsBaseChangeAutOf (AlgebraicClosure ℚ) (ModularCurve.diamondAut M d) σ')
    (d d' : ℕ) (hd : Nat.Coprime d M) (hd' : Nat.Coprime d' M) :
    ModularCurve.diamondOneBar M (d * d') =
      ModularCurve.diamondOneBar M d * ModularCurve.diamondOneBar M d' := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_diamondOneBar_mul_of_coprime.solution
