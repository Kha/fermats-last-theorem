import Mathlib
import Definitions.Def_CuspForm_AtkinLehnerOperator
import Definitions.Def_ModularForm_HeckeOperatorForms
import Definitions.Def_CuspForm_LevelLoweringTrace
import Theorems.Thm_CuspForm_atkinLehnerLin_atkinLehnerLin
import Theorems.Thm_ModularForm_S2_Gamma0_one_eq_zero
import P2M.Util
namespace P2MW.S_CuspForm_heckeULin_eq_neg_atkinLehnerLin_of_prime_level

set_option autoImplicit false

open ModularForm

theorem solution {ℓ : ℕ} [NeZero ℓ] (hℓ : ℓ.Prime)
    (A : ModularForm.AtkinLehnerDatum ℓ ℓ) (f : CuspForm (CongruenceSubgroup.Gamma0 ℓ) 2) :
    CuspForm.heckeULin 2 (dvd_refl ℓ) f = -CuspForm.atkinLehnerLin A 2 f := by

  have hR : A.R = 1 := by
    have h := A.hM
    have hpos : 0 < ℓ := Nat.pos_of_ne_zero (NeZero.ne ℓ)
    have : ℓ * A.R = ℓ * 1 := by rw [mul_one]; exact h.symm
    exact Nat.eq_of_mul_eq_mul_left hpos this
  have hzero : ∀ (R : ℕ) (_ : R = 1) (g : CuspForm (CongruenceSubgroup.Gamma0 R) 2), g = 0 := by
    rintro R rfl g
    exact ModularForm.S2_Gamma0_one_eq_zero g
  have h2 : CuspForm.traceLin A hℓ (CuspForm.atkinLehnerLin A 2 f) = 0 := hzero A.R hR _

  refine DFunLike.coe_injective ?_
  have h := congrArg (fun g : CuspForm (CongruenceSubgroup.Gamma0 A.R) 2 => (⇑g : UpperHalfPlane → ℂ)) h2
  have hww : alSlash A 2 (alSlash A 2 ⇑f) = ⇑f := by
    have := congrArg (fun g : CuspForm (CongruenceSubgroup.Gamma0 ℓ) 2 => (⇑g : UpperHalfPlane → ℂ))
      (CuspForm.atkinLehnerLin_atkinLehnerLin A f)
    simpa only [CuspForm.coe_atkinLehnerLin_apply] using this
  simp only [CuspForm.coe_traceLin_apply, CuspForm.coe_atkinLehnerLin_apply, CuspForm.coe_zero, hww] at h
  show heckeU 2 ℓ ⇑f = ⇑(-CuspForm.atkinLehnerLin A 2 f)
  rw [CuspForm.coe_neg, CuspForm.coe_atkinLehnerLin_apply]
  exact eq_neg_of_add_eq_zero_right h
