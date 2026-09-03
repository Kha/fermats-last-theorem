import Mathlib
import P2M.Util
import P2M.Sol.S_ValuationSubring_mem_inertiaSubgroup_map_subtype_iff

set_option autoImplicit false

open scoped Pointwise

theorem ValuationSubring.mem_inertiaSubgroup_map_subtype_iff
    {E F : Type*} [Field E] [Field F] [Algebra E F]
    (A : ValuationSubring F) (σ : F ≃ₐ[E] F) :
    σ ∈ (A.inertiaSubgroup E).map (A.decompositionSubgroup E).subtype ↔
      (∀ x : F, σ x ∈ A ↔ x ∈ A) ∧ ∀ a : F, a ∈ A → σ a - a ∈ A.nonunits := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_mem_inertiaSubgroup_map_subtype_iff.solution
