import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_exists_forall_not_isRoot_Psi3_specialization

open Polynomial
theorem WeierstrassCurve.exists_forall_not_isRoot_Psi3_specialization (a b : Polynomial ℚ) (ha : a.natDegree ≤ 20) (hb : b.natDegree ≤ 30) (hinf : 4 * a.coeff 20 ^ 3 + 27 * b.coeff 30 ^ 2 ≠ 0) (hroot : ∀ g : Polynomial ℚ, (⟨0, 0, 0, a, b⟩ : WeierstrassCurve (Polynomial ℚ)).Ψ₃.eval g ≠ 0) (M : ℕ) (hM : M ≠ 0) (m₀ : ℕ) : ∃ m : ℕ, m₀ ≤ m ∧ ∀ x : ℚ, ¬ (⟨0, 0, 0, a.eval ((M : ℚ) * m), b.eval ((M : ℚ) * m)⟩ : WeierstrassCurve ℚ).Ψ₃.IsRoot x := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_exists_forall_not_isRoot_Psi3_specialization.solution
