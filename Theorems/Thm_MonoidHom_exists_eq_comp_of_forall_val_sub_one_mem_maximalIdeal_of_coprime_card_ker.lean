import Mathlib
import Definitions.Def_Deformations_TameDescent
import P2M.Util
import P2M.Sol.S_MonoidHom_exists_eq_comp_of_forall_val_sub_one_mem_maximalIdeal_of_coprime_card_ker

set_option autoImplicit false

universe u v w
theorem MonoidHom.exists_eq_comp_of_forall_val_sub_one_mem_maximalIdeal_of_coprime_card_ker {G : Type u} {Δ : Type v} {R : Type w} [Group G] [Finite G] [Group Δ] [CommRing R] [IsLocalRing R]
    (π : G →* Δ) (hπ : Function.Surjective π) {p : ℕ} (hp : (p : R) ∈ IsLocalRing.maximalIdeal R)
    (hcop : (Nat.card π.ker).Coprime p)
    (ξ : G →* Rˣ) (hξ : ∀ g, (ξ g : R) - 1 ∈ IsLocalRing.maximalIdeal R) :
    ∃ χ : Δ →* Rˣ, ∀ g, ξ g = χ (π g) := by p2m_exact_reverting @_root_.P2MW.S_MonoidHom_exists_eq_comp_of_forall_val_sub_one_mem_maximalIdeal_of_coprime_card_ker.solution
