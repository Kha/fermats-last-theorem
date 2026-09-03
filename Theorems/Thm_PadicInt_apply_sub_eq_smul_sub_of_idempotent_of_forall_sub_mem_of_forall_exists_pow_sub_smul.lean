import Mathlib
import P2M.Util
import P2M.Sol.S_PadicInt_apply_sub_eq_smul_sub_of_idempotent_of_forall_sub_mem_of_forall_exists_pow_sub_smul

set_option autoImplicit false

theorem PadicInt.apply_sub_eq_smul_sub_of_idempotent_of_forall_sub_mem_of_forall_exists_pow_sub_smul
    (p : ℕ) [Fact p.Prime] {T : Type*} [AddCommGroup T] [Module ℤ_[p] T] [Module.Finite ℤ_[p] T]
    {ι : Type*} (I : Set ι) (ρ : ι → T →ₗ[ℤ_[p]] T) (χ : ι → ℤ_[p])
    (e U V : T →ₗ[ℤ_[p]] T) (he : ∀ x, e (e x) = e x)
    (heρ : ∀ g ∈ I, ∀ x, e (ρ g x) = ρ g (e x)) (hVρ : ∀ g ∈ I, ∀ x, V (ρ g x) = ρ g (V x))
    (heU : ∀ x, e (U x) = U (e x)) (heV : ∀ x, e (V x) = V (e x)) (hVU : ∀ x, V (U (e x)) = e x)
    (T₀ : Submodule ℤ_[p] T)
    (hKUM : ∀ g ∈ I, ∀ x : T, ρ g x - x ∈ T₀)
    (hSLP : ∃ N : ℕ, ∀ y ∈ T₀, ∃ z ∈ T₀, ∀ g ∈ I,
      ρ g ((U ^ N) y - (p : ℤ_[p]) • z) = χ g • ((U ^ N) y - (p : ℤ_[p]) • z)) :
    ∀ g ∈ I, ∀ h ∈ I, ∀ x : T, e x = x → ρ h (ρ g x - x) = χ h • (ρ g x - x) := by p2m_exact_reverting @_root_.P2MW.S_PadicInt_apply_sub_eq_smul_sub_of_idempotent_of_forall_sub_mem_of_forall_exists_pow_sub_smul.solution
