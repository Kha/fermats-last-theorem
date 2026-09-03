import Mathlib
import Definitions.Def_ModularCurve_SL2Elementary
import P2M.Util
import P2M.Sol.S_Matrix_SpecialLinearGroup_exists_subfield_forall_upperElem_mem_iff_of_finite

set_option autoImplicit false

open Matrix MatrixGroups

theorem Matrix.SpecialLinearGroup.exists_subfield_forall_upperElem_mem_iff_of_finite
    {K : Type} [Field K] {p : ℕ} [Fact p.Prime] [CharP K p] (hp2 : p ≠ 2)
    (G : Subgroup SL(2, K)) [Finite G]
    (hU : ModularCurve.upperElem (1 : K) ∈ G)
    (hL : ∃ μ : K, μ ≠ 0 ∧ ModularCurve.lowerElem μ ∈ G) :
    (p = 3 ∧ ∀ t : K, ModularCurve.upperElem t ∈ G → t ^ 3 = t) ∨
    ∃ F : Subfield K, Finite F ∧
      (∀ t : K, ModularCurve.upperElem t ∈ G ↔ t ∈ F) ∧
      (∀ t : K, ModularCurve.lowerElem t ∈ G ↔ t ∈ F) := by p2m_exact_reverting @_root_.P2MW.S_Matrix_SpecialLinearGroup_exists_subfield_forall_upperElem_mem_iff_of_finite.solution
