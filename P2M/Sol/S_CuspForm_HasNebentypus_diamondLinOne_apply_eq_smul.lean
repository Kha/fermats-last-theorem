import Mathlib
import Definitions.Def_CuspForm_PrimitiveFormGamma1
import Definitions.Def_CuspForm_Gamma1HeckeOperators
import P2M.Util
namespace P2MW.S_CuspForm_HasNebentypus_diamondLinOne_apply_eq_smul

set_option autoImplicit false

open CongruenceSubgroup ModularForm UpperHalfPlane
open scoped MatrixGroups ModularForm

theorem solution {M : ℕ} {k : ℤ}
    {ε : DirichletCharacter ℂ M} {g : CuspForm (CongruenceSubgroup.Gamma1 M) k}
    (hg : CuspForm.HasNebentypus ε g) {d : ℕ} (hd : Nat.Coprime d M) :
    CuspForm.diamondLinOne M k d g = ε (d : ZMod M) • g := by
  obtain ⟨γ, hγ⟩ := CuspForm.exists_isDiamondLift_of_coprime hd
  refine CuspForm.ext fun τ => ?_
  rw [CuspForm.diamondLinOne_apply_apply hγ, CuspForm.IsGLPos.smul_apply, smul_eq_mul]

  have hs : ((⇑g : ℍ → ℂ) ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ γ)) τ
      = g (γ • τ) * denom (γ : GL (Fin 2) ℝ) τ ^ (-k) :=
    ModularForm.SL_slash_apply (f := ⇑g) (k := k) γ τ
  rw [hs, hg γ hγ.1 τ, hγ.2]
  have hden : denom (γ : GL (Fin 2) ℝ) τ = ((γ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 1 1 : ℤ) : ℂ) := by
    rw [ModularGroup.denom_apply]
  have hne : ((γ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 1 1 : ℤ) : ℂ) ≠ 0 := by
    rw [← hden]; exact denom_ne_zero _ τ
  rw [hden, zpow_neg, mul_assoc, mul_comm (_ ^ k * g τ), ← mul_assoc ((_) ^ k)⁻¹, inv_mul_cancel₀
    (zpow_ne_zero k hne), one_mul]
