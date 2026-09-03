import Mathlib
import Definitions.Def_GroupCohomology_CyclicCarry
import P2M.Util
import P2M.Sol.S_groupCohomology_infNatTrans_app_H2pi_carryFun_eq_card_nsmul

set_option autoImplicit false
open CategoryTheory groupCohomology

theorem groupCohomology.infNatTrans_app_H2pi_carryFun_eq_card_nsmul
    {G : Type} [Group G] (s : G) (hs : ∀ g : G, g ∈ Subgroup.zpowers s) (hfin : IsOfFinOrder s)
    (N : Subgroup G) [N.Normal]
    (hsN : ∀ g : G ⧸ N, g ∈ Subgroup.zpowers (QuotientGroup.mk' N s)) (hsNfin : IsOfFinOrder (QuotientGroup.mk' N s))
    {A : Rep ℤ G} (a : A.quotientToInvariants N)
    (hc : carryFun (A := A) s hs hfin a.1 ∈ cocycles₂ A)
    (hcN : carryFun (QuotientGroup.mk' N s) hsN hsNfin a ∈ cocycles₂ (A.quotientToInvariants N)) :
    ((infNatTrans ℤ N 2).app A).hom
      ((H2π (A.quotientToInvariants N)).hom
        ⟨carryFun (QuotientGroup.mk' N s) hsN hsNfin a, hcN⟩) =
      Nat.card N • (H2π A).hom ⟨carryFun (A := A) s hs hfin a.1, hc⟩ := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_infNatTrans_app_H2pi_carryFun_eq_card_nsmul.solution
