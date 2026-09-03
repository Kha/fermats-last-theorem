import Mathlib
import Definitions.Def_GroupCohomology_CyclicCarry
import P2M.Util
import P2M.Sol.S_groupCohomology_carry_H2pi_add

set_option autoImplicit false
open CategoryTheory groupCohomology
theorem groupCohomology.carry_H2pi_add {G : Type} [Group G] (s : G) (hs : ∀ g : G, g ∈ Subgroup.zpowers s) (hfin : IsOfFinOrder s)
    {A : Rep ℤ G} (a b : A) (ha : carryFun s hs hfin a ∈ cocycles₂ A) (hb : carryFun s hs hfin b ∈ cocycles₂ A)
    (hab : carryFun s hs hfin (a + b) ∈ cocycles₂ A) :
    (H2π A).hom ⟨carryFun s hs hfin (a + b), hab⟩ =
      (H2π A).hom ⟨carryFun s hs hfin a, ha⟩ + (H2π A).hom ⟨carryFun s hs hfin b, hb⟩ := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_carry_H2pi_add.solution
