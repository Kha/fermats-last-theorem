import Mathlib
import Theorems.Thm_FiniteField_exists_forall_affineMap_ne_zero
import P2M.Util
import P2M.Sol.S_FiniteField_exists_forall_affineMap_apply_ne_zero_of_forall_lt

set_option autoImplicit false

theorem FiniteField.exists_forall_affineMap_apply_ne_zero_of_forall_lt
    {𝔽 : Type*} [Field 𝔽] [Fintype 𝔽] {s : ℕ} {n : Fin s → ℕ}
    {ι : Fin s → Type*} [∀ i, Fintype (ι i)]
    {V : ∀ i, ι i → Type*} [∀ i j, AddCommGroup (V i j)] [∀ i j, Module 𝔽 (V i j)]
    (φ : ∀ i, (∀ i' : Fin s, Fin (n i') → 𝔽) → ∀ j : ι i, (Fin (n i) → 𝔽) →ᵃ[𝔽] V i j)
    (hdep : ∀ i (x x' : ∀ i' : Fin s, Fin (n i') → 𝔽), (∀ i', i' < i → x i' = x' i') → φ i x = φ i x')
    (hφ : ∀ i x j, ∃ y, φ i x j y ≠ 0)
    (hm : ∀ i, Fintype.card (ι i) < Fintype.card 𝔽) :
    ∃ x : ∀ i : Fin s, Fin (n i) → 𝔽, ∀ i j, φ i x j (x i) ≠ 0 := by p2m_exact_reverting @_root_.P2MW.S_FiniteField_exists_forall_affineMap_apply_ne_zero_of_forall_lt.solution
