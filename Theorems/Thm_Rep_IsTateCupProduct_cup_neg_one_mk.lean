import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Definitions.Def_GroupCohomology_TateSeam
import Definitions.Def_GroupCohomology_TateShiftMaps
import Definitions.Def_GroupCohomology_CochainCup
import Definitions.Def_GroupCohomology_IsGradedCupProduct
import Definitions.Def_GroupCohomology_IsTateCupProduct
import P2M.Util
import P2M.Sol.S_Rep_IsTateCupProduct_cup_neg_one_mk

set_option autoImplicit false
universe u
open CategoryTheory Rep MonoidalCategory
theorem Rep.IsTateCupProduct.cup_neg_one_mk {k G : Type u} [CommRing k] [Group G] [Fintype G]
    {cup : Rep.TateCupFamily k G} (hcup : Rep.IsTateCupProduct cup) (A B : Rep.{u} k G)
    (x : A.tateHneg1) (a₀ : A) (hx : (x : A.ρ.Coinvariants) = Representation.Coinvariants.mk A.ρ a₀)
    (b : B.ρ.invariants) (z : (A ⊗ B).tateHneg1)
    (hz : (z : (A ⊗ B).ρ.Coinvariants) = Representation.Coinvariants.mk (A ⊗ B).ρ (a₀ ⊗ₜ[k] (b : B))) :
    cup A B (-1) 0 (-1) (add_zero (-1)) x (Submodule.Quotient.mk b : B.tateH0) = z := by p2m_exact_reverting @_root_.P2MW.S_Rep_IsTateCupProduct_cup_neg_one_mk.solution
