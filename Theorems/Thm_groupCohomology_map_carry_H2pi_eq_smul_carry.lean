import Mathlib
import Definitions.Def_GroupCohomology_CyclicCarry
import P2M.Util
import P2M.Sol.S_groupCohomology_map_carry_H2pi_eq_smul_carry

set_option autoImplicit false
open CategoryTheory groupCohomology
theorem groupCohomology.map_carry_H2pi_eq_smul_carry {G : Type} [Group G] {H : Type} [Group H] (j : H →* G) (hj : Function.Injective j)
    (s : G) (hs : ∀ g : G, g ∈ Subgroup.zpowers s) (hfins : IsOfFinOrder s)
    (f : ℕ) (t : H) (hjt : j t = s ^ f) (ht : ∀ h : H, h ∈ Subgroup.zpowers t) (hfint : IsOfFinOrder t)
    (A : Rep ℤ G) (B : Rep ℤ H) (φ : Rep.res j A ⟶ B)
    (a : A) (ha : A.ρ s a = a)
    (hza : carryFun s hs hfins a ∈ cocycles₂ A)
    (hzb : carryFun t ht hfint (φ.hom a) ∈ cocycles₂ B) :
    (groupCohomology.map j φ 2).hom ((H2π A).hom ⟨carryFun s hs hfins a, hza⟩) =
      (f / Nat.gcd (orderOf s) f) • (H2π B).hom ⟨carryFun t ht hfint (φ.hom a), hzb⟩ := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_map_carry_H2pi_eq_smul_carry.solution
