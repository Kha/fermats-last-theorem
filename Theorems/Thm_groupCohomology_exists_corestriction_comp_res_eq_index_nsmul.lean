import Mathlib
import P2M.Util
import P2M.Sol.S_groupCohomology_exists_corestriction_comp_res_eq_index_nsmul
set_option autoImplicit false
open CategoryTheory

theorem groupCohomology.exists_corestriction_comp_res_eq_index_nsmul
    {G : Type} [Group G] (H : Subgroup G) [H.FiniteIndex] (M : Rep ℤ G) (n : ℕ) :
    ∃ cor : groupCohomology (Rep.res H.subtype M) n →+ groupCohomology M n,
      ∀ x : groupCohomology M n,
        cor ((groupCohomology.map H.subtype (𝟙 (Rep.res H.subtype M)) n).hom x) = H.index • x := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_exists_corestriction_comp_res_eq_index_nsmul.solution
