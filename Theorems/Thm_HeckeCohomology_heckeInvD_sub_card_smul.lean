import Definitions.Def_GroupCohomology_DClassCoeff
import P2M.Util
import P2M.Sol.S_HeckeCohomology_heckeInvD_sub_card_smul

set_option autoImplicit false
attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

theorem HeckeCohomology.heckeInvD_sub_card_smul {k : Type} [CommRing k] (M : ℕ)
    (H : Subgroup (ZMod M)ˣ) (ℓ : ℕ) [NeZero ℓ] (A : Rep k ↥(CohCarrier.GammaH M H))
    (hA : IsDClass M H A) (z : A.ρ.invariants) :
    heckeInvD M H ℓ A hA z -
      Fintype.card (Quotient (QuotientGroup.rightRel (CohCarrier.GammaHUpper M H ℓ))) • z = 0 := by p2m_exact_reverting @_root_.P2MW.S_HeckeCohomology_heckeInvD_sub_card_smul.solution
