import Mathlib
import Definitions.Def_ModularCurve_HeckeOperatorModL
import Theorems.Thm_ModularCurve_frobeniusPullbackModL_eq_zero_of_natCast_smul_eq_zero
import P2M.Util
namespace P2MW.S_ModularCurve_heckeOperatorModL_eq_frobeniusPushforwardModL_of_natCast_smul_eq_zero
attribute [-simp] AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

open ModularCurve AlgebraicCurve

theorem solution
    (K : Type*) [Field K] [IsAlgClosed K] (ℓ : ℕ) [Fact ℓ.Prime] [CharP K ℓ] (N : ℕ) [NeZero N]
    (x : JZeroC K N) (hx : (ℓ : ℤ) • x = 0) :
    heckeOperatorModL K N ℓ x = frobeniusPushforwardModL K N ℓ x := by
  rw [heckeOperatorModL_apply, frobeniusPullbackModL_eq_zero_of_natCast_smul_eq_zero K ℓ N x hx, add_zero]
