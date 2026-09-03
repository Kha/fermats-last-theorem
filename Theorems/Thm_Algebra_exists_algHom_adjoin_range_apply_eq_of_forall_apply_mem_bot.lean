import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_exists_algHom_adjoin_range_apply_eq_of_forall_apply_mem_bot

set_option autoImplicit false

theorem Algebra.exists_algHom_adjoin_range_apply_eq_of_forall_apply_mem_bot
    {κ : Type*} [Field κ] {B : Type*} [Ring B] [Algebra κ B]
    {ι : Type*} (c : ι → (B →ₗ[κ] κ)) (hc : ∀ b : B, (∀ i, c i b = 0) → b = 0)
    {T : Type*} [CommRing T] (red : T →+* B) (ρ : T →+* κ)
    (hbot : ∀ (t : T) (i : ι), c i (red t) ∈ (⊥ : Subfield κ))
    (hker : ∀ t : T, red t = 0 → ρ t = 0) :
    ∃ χ : ↥(Algebra.adjoin κ (Set.range red)) →ₐ[κ] κ,
      ∀ t : T, χ ⟨red t, Algebra.subset_adjoin (Set.mem_range_self t)⟩ = ρ t := by p2m_exact_reverting @_root_.P2MW.S_Algebra_exists_algHom_adjoin_range_apply_eq_of_forall_apply_mem_bot.solution
