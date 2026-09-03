import Mathlib
import Definitions.Def_GroupCohomology_CyclicCarry
import P2M.Util
import P2M.Sol.S_groupCohomology_exists_carry_H2pi_eq

set_option autoImplicit false
open CategoryTheory groupCohomology
theorem groupCohomology.exists_carry_H2pi_eq {G : Type} [Group G] (s : G) (hs : ∀ g : G, g ∈ Subgroup.zpowers s) (hfin : IsOfFinOrder s)
    {A : Rep ℤ G} (c : cocycles₂ A) :
    A.ρ s (cyclicInv s ⇑c) = cyclicInv s ⇑c ∧
    ∃ h : carryFun s hs hfin (cyclicInv s ⇑c) ∈ cocycles₂ A,
      (H2π A).hom ⟨carryFun s hs hfin (cyclicInv s ⇑c), h⟩ = (H2π A).hom c := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_exists_carry_H2pi_eq.solution
