import Mathlib
import Definitions.Def_ModularCurve_HeckeOperatorModL
import P2M.Util
import P2M.Sol.S_ModularCurve_heckeOperatorModL_eq_frobeniusPushforwardModL_of_natCast_smul_eq_zero
attribute [-simp] AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero

set_option autoImplicit false

open ModularCurve AlgebraicCurve
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

theorem ModularCurve.heckeOperatorModL_eq_frobeniusPushforwardModL_of_natCast_smul_eq_zero
    (K : Type*) [Field K] [IsAlgClosed K] (ℓ : ℕ) [Fact ℓ.Prime] [CharP K ℓ] (N : ℕ) [NeZero N]
    (x : JZeroC K N) (hx : (ℓ : ℤ) • x = 0) :
    heckeOperatorModL K N ℓ x = frobeniusPushforwardModL K N ℓ x := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_heckeOperatorModL_eq_frobeniusPushforwardModL_of_natCast_smul_eq_zero.solution
