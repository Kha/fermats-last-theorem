import Mathlib
import P2M.Util
import P2M.Sol.S_Submodule_finiteDimensional_and_finrank_le_of_forall_orthonormal_card_le_of_definite

set_option autoImplicit false

open scoped ComplexConjugate

theorem Submodule.finiteDimensional_and_finrank_le_of_forall_orthonormal_card_le_of_definite
    {E : Type*} [AddCommGroup E] [Module ℂ E] (V : Submodule ℂ E)
    (B : E → E → ℂ)
    (hadd : ∀ x y z, B (x + y) z = B x z + B y z)
    (hsmul : ∀ (c : ℂ) (x y : E), B (c • x) y = c * B x y)
    (hsymm : ∀ x y, B y x = conj (B x y))
    (hpos : ∀ x ∈ V, 0 ≤ (B x x).re)
    (hdef : ∀ x ∈ V, B x x = 0 → x = 0)
    (D : ℕ) (hD : ∀ (n : ℕ) (e : Fin n → E), (∀ i, e i ∈ V) →
      (∀ i j, B (e i) (e j) = if i = j then 1 else 0) → n ≤ D) :
    FiniteDimensional ℂ V ∧ Module.finrank ℂ V ≤ D := by p2m_exact_reverting @_root_.P2MW.S_Submodule_finiteDimensional_and_finrank_le_of_forall_orthonormal_card_le_of_definite.solution
