import Mathlib
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_Affine_Point_zmultiples_eq_of_forall_isRoot_iff_of_addOrderOf_eq

set_option autoImplicit false

theorem WeierstrassCurve.Affine.Point.zmultiples_eq_of_forall_isRoot_iff_of_addOrderOf_eq
    (Ω : Type) [Field Ω] [DecidableEq Ω] (W : WeierstrassCurve Ω) (M' : ℕ) [NeZero M']
    (H : AddSubgroup W.toAffine.Point) (hH : IsAddCyclic H ∧ Nat.card H = M')
    (h : ↥M'.primeFactors → Polynomial Ω) (h0 : ∀ p, h p ≠ 0)
    (hroots : ∀ (p : ↥M'.primeFactors) (x₁ : Ω),
      (h p).IsRoot x₁ ↔ ∃ (P : W.toAffine.Point) (y₁ : Ω) (h₁ : W.toAffine.Nonsingular x₁ y₁),
        P ∈ H ∧ addOrderOf P = (p : ℕ) ^ M'.factorization (p : ℕ) ∧ P = WeierstrassCurve.Affine.Point.some x₁ y₁ h₁)
    (g : W.toAffine.Point)
    (hg : addOrderOf g = M' ∧
      ∀ (p : ↥M'.primeFactors) (n : ℕ) (x₁ y₁ : Ω) (h₁ : W.toAffine.Nonsingular x₁ y₁),
        n • g = WeierstrassCurve.Affine.Point.some x₁ y₁ h₁ → addOrderOf (n • g) = (p : ℕ) ^ M'.factorization (p : ℕ) →
        (h p).IsRoot x₁) :
    AddSubgroup.zmultiples g = H := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_Affine_Point_zmultiples_eq_of_forall_isRoot_iff_of_addOrderOf_eq.solution
