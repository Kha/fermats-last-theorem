import Mathlib
import P2M.Util
import P2M.Sol.S_PadicInt_exists_pow_smul_mem_sup_of_forall_bilinForm_apply_eq_zero

set_option autoImplicit false

open scoped TensorProduct

theorem PadicInt.exists_pow_smul_mem_sup_of_forall_bilinForm_apply_eq_zero
    {p : ℕ} [Fact p.Prime] {T : Type*} [AddCommGroup T] [Module ℤ_[p] T] [Module.Finite ℤ_[p] T] {Γ : Type*} [Group Γ]
    (ρ : Γ →* Module.End ℤ_[p] T) (χ : Γ →* ℤ_[p]ˣ) (I : Subgroup Γ)
    (e : LinearMap.BilinForm ℤ_[p] T)
    (hskew : ∀ a b : T, e a b = - e b a)
    (hnondeg : ∀ a : T, (∀ b : T, e a b = 0) → a = 0)
    (hequiv : ∀ (γ : Γ) (a b : T), e (ρ γ a) (ρ γ b) = ((χ γ : ℤ_[p]ˣ) : ℤ_[p]) * e a b)
    (Tt To : Submodule ℤ_[p] T)
    (hTt : ∀ γ ∈ I, ∀ x ∈ Tt, ρ γ x ∈ Tt)
    (hTo : ∀ γ ∈ I, ∀ y ∈ To, ρ γ y ∈ To)
    (hISO : ∀ x ∈ Tt, ∀ y ∈ To, e x y = 0)
    (hCUT : ∃ k : ℕ, ∀ τ ∈ I, ∀ v : T, ((p : ℤ_[p]) ^ k) • (ρ τ v - v) ∈ Tt ⊔ To)
    (hOLD : ∀ y ∈ To, (∀ y' ∈ To, e y y' = 0) → y = 0)
    (hCYC : ∃ τ₀ ∈ I, χ τ₀ ≠ 1) :
    ∃ k : ℕ, ∀ v : T, (∀ x ∈ Tt, e v x = 0) → ((p : ℤ_[p]) ^ k) • v ∈ Tt ⊔ To := by p2m_exact_reverting @_root_.P2MW.S_PadicInt_exists_pow_smul_mem_sup_of_forall_bilinForm_apply_eq_zero.solution
