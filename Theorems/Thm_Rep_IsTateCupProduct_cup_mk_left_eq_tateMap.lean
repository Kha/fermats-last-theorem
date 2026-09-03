import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Definitions.Def_GroupCohomology_TateSeam
import Definitions.Def_GroupCohomology_TateShiftMaps
import Definitions.Def_GroupCohomology_CochainCup
import Definitions.Def_GroupCohomology_IsGradedCupProduct
import Definitions.Def_GroupCohomology_IsTateCupProduct
import P2M.Util
import P2M.Sol.S_Rep_IsTateCupProduct_cup_mk_left_eq_tateMap

set_option autoImplicit false
universe u
open CategoryTheory Rep MonoidalCategory
theorem Rep.IsTateCupProduct.cup_mk_left_eq_tateMap {k G : Type u} [CommRing k] [Group G] [Fintype G]
    {cup : Rep.TateCupFamily k G} (hcup : Rep.IsTateCupProduct cup) (A B : Rep.{u} k G)
    (a : A.ρ.invariants) (φ : B ⟶ A ⊗ B) (hφ : ∀ b : B, φ.hom b = (a : A) ⊗ₜ[k] b)
    (q : ℤ) (y : B.tateCohomology q) :
    cup A B 0 q q (zero_add q) (Submodule.Quotient.mk a : A.tateH0) y = (Rep.tateMap φ q).hom y := by p2m_exact_reverting @_root_.P2MW.S_Rep_IsTateCupProduct_cup_mk_left_eq_tateMap.solution
