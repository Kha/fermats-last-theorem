import Mathlib
import P2M.Util
import P2M.Sol.S_IsLocallyConstant_exists_isOpen_one_mem_forall_mul_eq_of_hasCompactSupport

set_option autoImplicit false
theorem IsLocallyConstant.exists_isOpen_one_mem_forall_mul_eq_of_hasCompactSupport
    {G M : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Zero M]
    (Φ : G → M) (hlc : IsLocallyConstant Φ) (hcs : HasCompactSupport Φ) :
    ∃ W : Set G, IsOpen W ∧ (1 : G) ∈ W ∧
      ∀ g : G, ∀ w ∈ W, Φ (g * w) = Φ g ∧ Φ (w * g) = Φ g := by p2m_exact_reverting @_root_.P2MW.S_IsLocallyConstant_exists_isOpen_one_mem_forall_mul_eq_of_hasCompactSupport.solution
