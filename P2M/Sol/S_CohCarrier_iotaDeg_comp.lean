import Definitions.Def_CohCarrier_Level
import P2M.Util
namespace P2MW.S_CohCarrier_iotaDeg_comp

set_option autoImplicit false
open scoped MatrixGroups
open CohCarrier

theorem solution {M₁ M₂ M₃ d₁ d₂ : ℕ} {H₁ : Subgroup (ZMod M₁)ˣ} {H₂ : Subgroup (ZMod M₂)ˣ}
    {H₃ : Subgroup (ZMod M₃)ˣ}
    [NeZero M₂] [NeZero M₃] [NeZero d₁] [NeZero d₂] [NeZero (d₁ * d₂)]
    (h₁₂ : LevelLE M₁ M₂ H₁ H₂ d₁) (h₂₃ : LevelLE M₂ M₃ H₂ H₃ d₂)
    (h₁₃ : LevelLE M₁ M₃ H₁ H₃ (d₁ * d₂)) (γ : ↥(GammaH M₃ H₃)) :
    iotaDeg M₁ M₃ H₁ H₃ (d₁ * d₂) h₁₃ γ
      = iotaDeg M₁ M₂ H₁ H₂ d₁ h₁₂ (iotaDeg M₂ M₃ H₂ H₃ d₂ h₂₃ γ) := by
  apply Subtype.ext
  show conjLowerMat (d₁ * d₂) (γ : SL(2, ℤ)) (h₁₃.dvd_entry γ)
    = conjLowerMat d₁ (conjLowerMat d₂ (γ : SL(2, ℤ)) (h₂₃.dvd_entry γ))
        (h₁₂.dvd_entry (iotaDeg M₂ M₃ H₂ H₃ d₂ h₂₃ γ))
  have hd₁ : (d₁ : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d₁)
  have hd₂ : (d₂ : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d₂)
  obtain ⟨k, hk⟩ := h₁₃.dvd_entry γ
  push_cast at hk
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp only [conjLowerMat, Matrix.of_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Fin.isValue]
  · rfl
  · push_cast; ring
  · push_cast
    rw [hk, Int.mul_ediv_cancel_left _ (mul_ne_zero hd₁ hd₂),
      show (d₁ : ℤ) * d₂ * k = d₂ * (d₁ * k) from by ring,
      Int.mul_ediv_cancel_left _ hd₂, Int.mul_ediv_cancel_left _ hd₁]
  · rfl

#print axioms solution
