import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Definitions.Def_GroupCohomology_TateSeam
import Definitions.Def_GroupCohomology_TateShiftMaps
import Definitions.Def_GroupCohomology_CochainCup
import Definitions.Def_GroupCohomology_IsGradedCupProduct
import Definitions.Def_GroupCohomology_IsTateCupProduct
import P2M.Util
import P2M.Sol.S_Rep_IsTateCupProduct_cup_mk_right_eq_tateMap

set_option autoImplicit false
universe u
open CategoryTheory Rep MonoidalCategory
theorem Rep.IsTateCupProduct.cup_mk_right_eq_tateMap {k G : Type u} [CommRing k] [Group G] [Fintype G]
    {cup : Rep.TateCupFamily k G} (hcup : Rep.IsTateCupProduct cup) (A B : Rep.{u} k G)
    (b : B.ρ.invariants) (ψ : A ⟶ A ⊗ B) (hψ : ∀ a : A, ψ.hom a = a ⊗ₜ[k] (b : B))
    (p : ℤ) (x : A.tateCohomology p) :
    cup A B p 0 p (add_zero p) x (Submodule.Quotient.mk b : B.tateH0) = (Rep.tateMap ψ p).hom x := by p2m_exact_reverting @_root_.P2MW.S_Rep_IsTateCupProduct_cup_mk_right_eq_tateMap.solution
