import Mathlib
import P2M.Util
import P2M.Sol.S_Subgroup_exists_int_forall_finsum_ite_eq_one

set_option autoImplicit false

open CategoryTheory MonoidalCategory Module
open scoped Classical

theorem Subgroup.exists_int_forall_finsum_ite_eq_one (p : ℕ) {G : Type} [Group G] [Finite G] :
    ∃ b : Subgroup G → ℤ, ∀ H : Subgroup G, IsCyclic H → (Nat.card H).Coprime p →
      ∑ᶠ D : Subgroup G, (if IsCyclic D ∧ (Nat.card D).Coprime p ∧ H ≤ D then b D else 0) = 1 := by p2m_exact_reverting @_root_.P2MW.S_Subgroup_exists_int_forall_finsum_ite_eq_one.solution
