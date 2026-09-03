import Mathlib
import P2M.Util
import P2M.Sol.S_CuspForm_intervalIntegral_slash_vadd_eq_zero

set_option autoImplicit false

open scoped MatrixGroups ModularForm

theorem CuspForm.intervalIntegral_slash_vadd_eq_zero
    {M : ℕ} [NeZero M] {k : ℤ} (h : CuspForm (CongruenceSubgroup.Gamma1 M) k) (ρ : SL(2, ℤ))
    (z : UpperHalfPlane) :
    ∫ s in (0 : ℝ)..(M : ℝ), ((⇑h) ∣[k] (ρ : GL (Fin 2) ℝ)) (s +ᵥ z) = 0 := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_intervalIntegral_slash_vadd_eq_zero.solution
