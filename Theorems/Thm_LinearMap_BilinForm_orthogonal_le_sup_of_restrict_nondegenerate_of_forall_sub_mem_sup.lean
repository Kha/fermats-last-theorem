import Mathlib
import P2M.Util
import P2M.Sol.S_LinearMap_BilinForm_orthogonal_le_sup_of_restrict_nondegenerate_of_forall_sub_mem_sup

set_option autoImplicit false

theorem LinearMap.BilinForm.orthogonal_le_sup_of_restrict_nondegenerate_of_forall_sub_mem_sup
    {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {Γ : Type*} [Group Γ] (ρ : Representation K Γ V) (χ : Γ →* Kˣ)
    (I : Subgroup Γ)
    (e : LinearMap.BilinForm K V)
    (hrefl : ∀ a b : V, e a b = 0 → e b a = 0)
    (hnondeg : ∀ a : V, (∀ b : V, e a b = 0) → a = 0)
    (hequiv : ∀ (γ : Γ) (a b : V), e (ρ γ a) (ρ γ b) = ((χ γ : Kˣ) : K) * e a b)
    (Vt Vo : Submodule K V)
    (hVt : ∀ γ ∈ I, ∀ x ∈ Vt, ρ γ x ∈ Vt)
    (hVo : ∀ γ ∈ I, ∀ y ∈ Vo, ρ γ y ∈ Vo)
    (hISO : ∀ x ∈ Vt, ∀ y ∈ Vo, e x y = 0)
    (hCUT : ∀ τ ∈ I, ∀ v : V, ρ τ v - v ∈ Vt ⊔ Vo)
    (hOLD : ∀ y ∈ Vo, (∀ y' ∈ Vo, e y y' = 0) → y = 0)
    (hCYC : ∃ τ₀ ∈ I, χ τ₀ ≠ 1) :
    e.orthogonal Vt ≤ Vt ⊔ Vo := by p2m_exact_reverting @_root_.P2MW.S_LinearMap_BilinForm_orthogonal_le_sup_of_restrict_nondegenerate_of_forall_sub_mem_sup.solution
