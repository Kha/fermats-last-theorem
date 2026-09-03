import Mathlib
import Definitions.Def_ModularCurve_FrobeniusModL
import P2M.Util
import P2M.Sol.S_ModularCurve_frobeniusPullbackModL_eq_zero_of_natCast_smul_eq_zero
attribute [-simp] AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero

open ModularCurve AlgebraicCurve

theorem ModularCurve.frobeniusPullbackModL_eq_zero_of_natCast_smul_eq_zero
    (K : Type*) [Field K] [IsAlgClosed K] (ℓ : ℕ) [Fact ℓ.Prime] [CharP K ℓ] (N : ℕ) [NeZero N]
    (x : JZeroC K N) (hx : (ℓ : ℤ) • x = 0) :
    frobeniusPullbackModL K N ℓ x = 0 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_frobeniusPullbackModL_eq_zero_of_natCast_smul_eq_zero.solution
