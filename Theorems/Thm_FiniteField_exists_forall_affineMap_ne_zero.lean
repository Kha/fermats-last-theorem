import Mathlib
import P2M.Util
import P2M.Sol.S_FiniteField_exists_forall_affineMap_ne_zero

set_option autoImplicit false

theorem FiniteField.exists_forall_affineMap_ne_zero
    {𝔽 : Type*} [Field 𝔽] [Fintype 𝔽] {n : ℕ} {ι : Type*} [Fintype ι]
    {V : ι → Type*} [∀ j, AddCommGroup (V j)] [∀ j, Module 𝔽 (V j)]
    (φ : ∀ j, (Fin n → 𝔽) →ᵃ[𝔽] V j) (hφ : ∀ j, ∃ x, φ j x ≠ 0)
    (hm : Fintype.card ι < Fintype.card 𝔽) :
    ∃ x, ∀ j, φ j x ≠ 0 := by p2m_exact_reverting @_root_.P2MW.S_FiniteField_exists_forall_affineMap_ne_zero.solution
