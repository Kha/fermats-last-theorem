import Mathlib
import P2M.Util
import P2M.Sol.S_Rep_exists_isIrreducible_forall_additive_eq_sum

set_option autoImplicit false

open CategoryTheory MonoidalCategory Module
open scoped Classical

theorem Rep.exists_isIrreducible_forall_additive_eq_sum
    {k : Type} [Field k] {G : Type} [Group G]
    (A B : Rep.{0} k G) [FiniteDimensional k A] [FiniteDimensional k B] :
    ∃ (r : ℕ) (S : Fin r → Rep.{0} k G) (a b : Fin r → ℕ),
      (∀ i, FiniteDimensional k (S i) ∧ (S i).ρ.IsIrreducible) ∧
      (∀ i j, Nonempty (S i ≅ S j) → i = j) ∧
      ∀ φ : Rep.{0} k G → ℤ,
        (∀ X : ShortComplex (Rep.{0} k G), X.ShortExact → FiniteDimensional k X.X₂ →
          φ X.X₂ = φ X.X₁ + φ X.X₃) →
        φ A = ∑ i, (a i : ℤ) * φ (S i) ∧ φ B = ∑ i, (b i : ℤ) * φ (S i) := by p2m_exact_reverting @_root_.P2MW.S_Rep_exists_isIrreducible_forall_additive_eq_sum.solution
