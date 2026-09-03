import Mathlib
import P2M.Util
import P2M.Sol.S_UpperHalfPlane_cayley_smul_eq_mul_cayley

open UpperHalfPlane
open scoped MatrixGroups
theorem UpperHalfPlane.cayley_smul_eq_mul_cayley (γ : SL(2, ℤ)) (τ₀ : ℍ) (h : γ • τ₀ = τ₀) (τ : ℍ) :
    ((↑(γ • τ) : ℂ) - τ₀) / ((↑(γ • τ) : ℂ) - (starRingEnd ℂ) τ₀)
      = (((γ 1 0 : ℤ) : ℂ) * (starRingEnd ℂ) τ₀ + ((γ 1 1 : ℤ) : ℂ))
        / (((γ 1 0 : ℤ) : ℂ) * τ₀ + ((γ 1 1 : ℤ) : ℂ))
        * (((τ : ℂ) - τ₀) / ((τ : ℂ) - (starRingEnd ℂ) τ₀)) := by p2m_exact_reverting @_root_.P2MW.S_UpperHalfPlane_cayley_smul_eq_mul_cayley.solution
