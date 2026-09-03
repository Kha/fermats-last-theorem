import Definitions.Def_GroupCohomology_DClassCoeff
import P2M.Util
namespace P2MW.S_HeckeCohomology_heckeInvD_sub_card_smul

set_option autoImplicit false
attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

namespace TW12HInvAux

open CategoryTheory groupCohomology HeckeCohomology

variable {k : Type} [CommRing k] (M : ℕ) (H : Subgroup (ZMod M)ˣ) (ℓ : ℕ) [NeZero ℓ]

theorem invD_apply_eq (A : Rep k ↥(CohCarrier.GammaH M H)) (hA : IsDClass M H A)
    (z : A.ρ.invariants) :
    ((heckeInvD M H ℓ A hA z : A.ρ.invariants) : A) =
      Fintype.card (Quotient (QuotientGroup.rightRel (CohCarrier.GammaHUpper M H ℓ))) • (z : A) := by
  show ((heckeInv ⊤ (CohCarrier.GammaHUpper M H ℓ) (cTop M H ℓ) A LinearMap.id
    (isTwist_id_of_isDClass M H ℓ A hA) z : A.ρ.invariants) : A) = _
  rw [coe_heckeInv, norm0_apply]
  have hz : ∀ g : ↥(CohCarrier.GammaH M H), A.ρ g (z : A) = z :=
    (A.ρ.mem_invariants (z : A)).1 z.2
  simp_rw [LinearMap.id_apply, hz]
  rw [Finset.sum_const, Finset.card_univ]

end TW12HInvAux

open HeckeCohomology in
attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex in
theorem solution {k : Type} [CommRing k] (M : ℕ)
    (H : Subgroup (ZMod M)ˣ) (ℓ : ℕ) [NeZero ℓ] (A : Rep k ↥(CohCarrier.GammaH M H))
    (hA : IsDClass M H A) (z : A.ρ.invariants) :
    heckeInvD M H ℓ A hA z -
      Fintype.card (Quotient (QuotientGroup.rightRel (CohCarrier.GammaHUpper M H ℓ))) • z = 0 := by
  rw [sub_eq_zero]
  apply Subtype.ext
  rw [TW12HInvAux.invD_apply_eq]
  rfl
