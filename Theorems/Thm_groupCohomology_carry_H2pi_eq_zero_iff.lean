import Mathlib
import Definitions.Def_GroupCohomology_CyclicCarry
import P2M.Util
import P2M.Sol.S_groupCohomology_carry_H2pi_eq_zero_iff

set_option autoImplicit false
open CategoryTheory groupCohomology
theorem groupCohomology.carry_H2pi_eq_zero_iff {G : Type} [Group G] (s : G) (hs : ∀ g : G, g ∈ Subgroup.zpowers s) (hfin : IsOfFinOrder s)
    {A : Rep ℤ G} (a : A) (ha : A.ρ s a = a) (h : carryFun s hs hfin a ∈ cocycles₂ A) :
    (H2π A).hom ⟨carryFun s hs hfin a, h⟩ = 0 ↔
      ∃ b : A, (∑ i ∈ Finset.range (orderOf s), A.ρ (s ^ i) b) = a := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_carry_H2pi_eq_zero_iff.solution
