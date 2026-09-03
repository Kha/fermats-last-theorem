import Mathlib
import Definitions.Def_ModularCurve_X1HeckeModule
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_AlgebraicCurve_Pic0Congr
import P2M.Util
import P2M.Sol.S_ModularCurve_pic0Congr_jOne_jH_bot_compat

set_option autoImplicit false

theorem ModularCurve.pic0Congr_jOne_jH_bot_compat (M : ℕ) [NeZero M]
    (hin : ModularCurve.HeckeDiamondInputsAll M) (hinH : ModularCurve.HeckeDiamondInputsHAll M ⊥)
    (h : ModularCurve.x1FunctionFieldBar M = ModularCurve.xHFunctionFieldBar M ⊥) :
    let e : ModularCurve.JOne M ≃+ ModularCurve.JH M ⊥ :=
      AlgebraicCurve.Pic0.congr (IntermediateField.equivOfEq h).toRingEquiv
        (IntermediateField.equivOfEq h).commutes
    (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (x : ModularCurve.JOne M),
        e (ModularCurve.heckeOperatorOneBar M ⟨ℓ, hℓ⟩ x) =
          (haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩;
            ModularCurve.heckeOperatorHAlong (AlgebraicClosure ℚ) M ⊥ ℓ) (e x)) ∧
    (∀ (d : ℕ) (hd : d.Coprime M) (x : ModularCurve.JOne M),
        e (ModularCurve.diamondOneBar M d x) = ModularCurve.diamondHBar M ⊥ (ZMod.unitOfCoprime d hd) (e x)) ∧
    (∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : ModularCurve.JOne M),
        e (σ • x) = σ • e x) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_pic0Congr_jOne_jH_bot_compat.solution
