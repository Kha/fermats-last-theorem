import Mathlib
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_eq_zero_of_firstOrderVariableChange_eq_zero

set_option autoImplicit false

theorem WeierstrassCurve.eq_zero_of_firstOrderVariableChange_eq_zero
    (R : Type) [CommRing R] (E : WeierstrassCurve R) [E.IsElliptic] (μ ρ ς τ : R)
    (h₁ : E.a₁ * μ + 2 * ς = 0)
    (h₂ : 2 * E.a₂ * μ + 3 * ρ - E.a₁ * ς = 0)
    (h₃ : 3 * E.a₃ * μ + E.a₁ * ρ + 2 * τ = 0)
    (h₄ : 4 * E.a₄ * μ + 2 * E.a₂ * ρ - E.a₃ * ς - E.a₁ * τ = 0)
    (h₆ : 6 * E.a₆ * μ + E.a₄ * ρ - E.a₃ * τ = 0) :
    μ = 0 ∧ ρ = 0 ∧ ς = 0 ∧ τ = 0 := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_eq_zero_of_firstOrderVariableChange_eq_zero.solution
