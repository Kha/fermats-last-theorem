import Mathlib
import P2M.Util
import P2M.Sol.S_groupCohomology_exists_cor_map_res_two_eq_index_smul
attribute [-simp] groupCohomology.Cores.Transversal.mk.sizeOf_spec groupCohomology.Cores.Transversal.mk.injEq

set_option autoImplicit false
open CategoryTheory groupCohomology Rep

theorem groupCohomology.exists_cor_map_res_two_eq_index_smul
    {k G : Type} [CommRing k] [Group G] (X : Rep k G) (S : Subgroup G) [S.FiniteIndex] :
    ∃ cor : groupCohomology (Rep.res S.subtype X) 2 →ₗ[k] groupCohomology X 2,
      ∀ x : groupCohomology X 2,
        cor ((groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype X)) 2).hom x) = S.index • x := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_exists_cor_map_res_two_eq_index_smul.solution
