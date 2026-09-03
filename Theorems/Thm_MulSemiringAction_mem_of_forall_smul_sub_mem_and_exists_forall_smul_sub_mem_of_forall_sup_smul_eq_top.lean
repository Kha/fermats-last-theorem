import Mathlib
import P2M.Util
import P2M.Sol.S_MulSemiringAction_mem_of_forall_smul_sub_mem_and_exists_forall_smul_sub_mem_of_forall_sup_smul_eq_top

set_option autoImplicit false

open scoped Pointwise

theorem MulSemiringAction.mem_of_forall_smul_sub_mem_and_exists_forall_smul_sub_mem_of_forall_sup_smul_eq_top
    {B : Type*} [CommRing B] {G : Type*} [Group G] [Finite G] [MulSemiringAction G B]
    (I P : Ideal B) (hIP : I ≤ P) (hI : ∀ (g : G) (b : B), b ∈ I → g • b ∈ I)
    (hmax : ∀ g : G, g • P ≠ P → P ⊔ g • P = ⊤)
    (hinf : ∀ b : B, (∀ g : G, g • b ∈ P) → b ∈ I) :
    (∀ b : B, (∀ g : G, g • b - b ∈ I) → b ∈ P → b ∈ I) ∧
    (∀ s : B, (∀ g : G, g • P = P → g • s - s ∈ P) →
      ∃ r : B, (∀ g : G, g • r - r ∈ I) ∧ r - s ∈ P) := by p2m_exact_reverting @_root_.P2MW.S_MulSemiringAction_mem_of_forall_smul_sub_mem_and_exists_forall_smul_sub_mem_of_forall_sup_smul_eq_top.solution
