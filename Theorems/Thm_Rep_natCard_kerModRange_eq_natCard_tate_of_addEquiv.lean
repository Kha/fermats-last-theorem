import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import P2M.Util
import P2M.Sol.S_Rep_natCard_kerModRange_eq_natCard_tate_of_addEquiv

set_option autoImplicit false
open CategoryTheory Rep
theorem Rep.natCard_kerModRange_eq_natCard_tate_of_addEquiv {G : Type} [Group G] [Fintype G] (A : Rep ℤ G)
    (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g)
    {X : Type} [AddCommGroup X] (e : X ≃+ A)
    (d : X →+ X) (hd : ∀ x, e (d x) = A.ρ g (e x) - e x)
    (N : X →+ X) (hN : ∀ x, e (N x) = ∑ i ∈ Finset.range (Nat.card G), A.ρ (g ^ i) (e x)) :
    Nat.card (↥d.ker ⧸ N.range.addSubgroupOf d.ker) = Nat.card A.tateH0 ∧
      Nat.card (↥N.ker ⧸ d.range.addSubgroupOf N.ker) = Nat.card A.tateHneg1 := by p2m_exact_reverting @_root_.P2MW.S_Rep_natCard_kerModRange_eq_natCard_tate_of_addEquiv.solution
