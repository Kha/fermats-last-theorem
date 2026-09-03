import Mathlib
import Definitions.Def_CuspidalType_IsCuspidalOfType
import P2M.Util
import P2M.Sol.S_CuspidalType_exists_linearMap_apply_eq_self_of_forall_sum_unipotent_eq_zero_and_comm

set_option autoImplicit false

theorem CuspidalType.exists_linearMap_apply_eq_self_of_forall_sum_unipotent_eq_zero_and_comm
    (q : ℕ) [Fact q.Prime] (K : Type*) [Field K] [CharZero K]
    (V : Type*) [AddCommGroup V] [Module K V]
    (ρ : Representation K (CuspidalType.GL2 q) V)
    (Γ : Set (V →ₗ[K] V)) (hΓ : ∀ T ∈ Γ, ∀ g : CuspidalType.GL2 q, T ∘ₗ ρ g = ρ g ∘ₗ T) :
    ∃ eC : V →ₗ[K] V,
      (∀ v : V, (∀ g : CuspidalType.GL2 q, (∑ t : ZMod q, ρ (CuspidalType.unipotent q t) * ρ g) v = 0) → eC v = v) ∧
      (∀ g : CuspidalType.GL2 q, eC ∘ₗ ρ g = ρ g ∘ₗ eC) ∧
      (∀ T ∈ Γ, eC ∘ₗ T = T ∘ₗ eC) ∧
      (∀ (v : V) (g : CuspidalType.GL2 q), (∑ t : ZMod q, ρ (CuspidalType.unipotent q t) * ρ g) (eC v) = 0) := by p2m_exact_reverting @_root_.P2MW.S_CuspidalType_exists_linearMap_apply_eq_self_of_forall_sum_unipotent_eq_zero_and_comm.solution
