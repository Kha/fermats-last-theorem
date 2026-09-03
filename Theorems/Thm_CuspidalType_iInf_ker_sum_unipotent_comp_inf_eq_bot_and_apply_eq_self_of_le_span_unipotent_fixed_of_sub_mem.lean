import Definitions.Def_CuspidalType_IsCuspidalOfType
import P2M.Util
import P2M.Sol.S_CuspidalType_iInf_ker_sum_unipotent_comp_inf_eq_bot_and_apply_eq_self_of_le_span_unipotent_fixed_of_sub_mem

set_option autoImplicit false

theorem
    CuspidalType.iInf_ker_sum_unipotent_comp_inf_eq_bot_and_apply_eq_self_of_le_span_unipotent_fixed_of_sub_mem
    (q : ℕ) [Fact q.Prime] (K : Type) [Field K] [CharZero K] (V : Type) [AddCommGroup V] [Module K V]
    (ρ : Representation K (CuspidalType.GL2 q) V) (τ : V →ₗ[K] V)
    (hτ : ∀ g : CuspidalType.GL2 q, τ ∘ₗ ρ g = ρ g ∘ₗ τ)
    (T : Submodule K V)
    (hT : T ≤ Submodule.span K {x : V | ∃ (g : CuspidalType.GL2 q) (v : V),
      (∀ t : ZMod q, ρ (CuspidalType.unipotent q t) v = v) ∧ ρ g v = x})
    (hτT : ∀ v : V, τ v - v ∈ T) :
    (⨅ g : CuspidalType.GL2 q,
        LinearMap.ker (∑ t : ZMod q, ρ (CuspidalType.unipotent q t) ∘ₗ ρ g)) ⊓ T = ⊥ ∧
      ∀ v ∈ ⨅ g : CuspidalType.GL2 q,
        LinearMap.ker (∑ t : ZMod q, ρ (CuspidalType.unipotent q t) ∘ₗ ρ g), τ v = v := by p2m_exact_reverting @_root_.P2MW.S_CuspidalType_iInf_ker_sum_unipotent_comp_inf_eq_bot_and_apply_eq_self_of_le_span_unipotent_fixed_of_sub_mem.solution
