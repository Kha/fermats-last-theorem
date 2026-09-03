import Mathlib.Topology.Algebra.Valued.ValuationTopology
import Mathlib.FieldTheory.IsAlgClosed.Basic
import P2M.Util
import P2M.Sol.S_Polynomial_coeff_countP_roots_isDominant_of_isAlgClosed

set_option autoImplicit false

theorem Polynomial.coeff_countP_roots_isDominant_of_isAlgClosed
    (K : Type) [Field K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [IsAlgClosed K]
    (p : Polynomial K) (hp : p ≠ 0) :
    ((∀ j : ℕ, Valued.v (p.coeff j) ≤ Valued.v (p.coeff (p.roots.countP fun α => Valued.v α ≤ 1))) ∧
      ∀ j : ℕ, (p.roots.countP fun α => Valued.v α ≤ 1) < j →
        Valued.v (p.coeff j) < Valued.v (p.coeff (p.roots.countP fun α => Valued.v α ≤ 1))) ∧
    ((∀ j : ℕ, Valued.v (p.coeff j) ≤ Valued.v (p.coeff (p.roots.countP fun α => Valued.v α < 1))) ∧
      ∀ j : ℕ, j < (p.roots.countP fun α => Valued.v α < 1) →
        Valued.v (p.coeff j) < Valued.v (p.coeff (p.roots.countP fun α => Valued.v α < 1))) := by p2m_exact_reverting @_root_.P2MW.S_Polynomial_coeff_countP_roots_isDominant_of_isAlgClosed.solution
