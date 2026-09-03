import Mathlib
import Definitions.Def_GroupCohomology_CyclicCarry
import P2M.Util
import P2M.Sol.S_groupCohomology_carryFun_mem_cocycles2

set_option autoImplicit false
open CategoryTheory groupCohomology
theorem groupCohomology.carryFun_mem_cocycles2 {G : Type} [Group G] (s : G) (hs : ∀ g : G, g ∈ Subgroup.zpowers s) (hfin : IsOfFinOrder s)
    {A : Rep ℤ G} (a : A) (ha : A.ρ s a = a) :
    carryFun s hs hfin a ∈ cocycles₂ A := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_carryFun_mem_cocycles2.solution
