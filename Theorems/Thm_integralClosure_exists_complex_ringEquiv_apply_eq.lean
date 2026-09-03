import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import P2M.Util
import P2M.Sol.S_integralClosure_exists_complex_ringEquiv_apply_eq

theorem integralClosure.exists_complex_ringEquiv_apply_eq (k : Type*) [Field k]
    (φ ψ : integralClosure ℤ ℂ →+* k) :
    ∃ σ : ℂ ≃+* ℂ, ∀ x y : integralClosure ℤ ℂ, (y : ℂ) = σ (x : ℂ) → φ x = ψ y := by p2m_exact_reverting @_root_.P2MW.S_integralClosure_exists_complex_ringEquiv_apply_eq.solution
