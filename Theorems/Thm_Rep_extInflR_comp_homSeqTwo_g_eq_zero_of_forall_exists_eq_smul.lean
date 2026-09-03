import Mathlib
import Definitions.Def_GroupCohomology_RelationModule
import Definitions.Def_GroupCohomology_RelationModuleRes
import Definitions.Def_GroupCohomology_RepCokernel
import Definitions.Def_GroupCohomology_RepImage
import Definitions.Def_GroupCohomology_RelationHomDefect
import P2M.Util
import P2M.Sol.S_Rep_extInflR_comp_homSeqTwo_g_eq_zero_of_forall_exists_eq_smul

set_option autoImplicit false

open CategoryTheory

theorem Rep.extInflR_comp_homSeqTwo_g_eq_zero_of_forall_exists_eq_smul
    {G G' : Type} [Group G] [Group G'] (π : G' →* G) (B E : Rep ℤ G) [Fintype B] (E' : Rep ℤ G') (φ : Rep.res π E ⟶ E')
    (p : ℕ) [Fact p.Prime] (hB : ∀ b : B, p • b = 0) (hφ : ∀ e : E, ∃ e' : E', φ.hom e = p • e') :
    Rep.extInflR π B E E' φ ≫ (Rep.homSeq₂ (Rep.res π B) E').g = 0 := by p2m_exact_reverting @_root_.P2MW.S_Rep_extInflR_comp_homSeqTwo_g_eq_zero_of_forall_exists_eq_smul.solution
