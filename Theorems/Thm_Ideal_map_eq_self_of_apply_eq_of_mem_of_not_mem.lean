import Mathlib
import P2M.Util
import P2M.Sol.S_Ideal_map_eq_self_of_apply_eq_of_mem_of_not_mem

set_option autoImplicit false

theorem Ideal.map_eq_self_of_apply_eq_of_mem_of_not_mem
    {S : Type*} [CommRing S] (γ : S ≃+* S) {P₁ P₂ : Ideal S}
    (h₁ : P₁.map (γ : S →+* S) = P₁ ∨ P₁.map (γ : S →+* S) = P₂)
    (h₂ : P₂.map (γ : S →+* S) = P₁ ∨ P₂.map (γ : S →+* S) = P₂)
    {a : S} (hγa : γ a = a) (ha₁ : a ∈ P₁) (ha₂ : a ∉ P₂) :
    P₁.map (γ : S →+* S) = P₁ ∧ P₂.map (γ : S →+* S) = P₂ := by p2m_exact_reverting @_root_.P2MW.S_Ideal_map_eq_self_of_apply_eq_of_mem_of_not_mem.solution
