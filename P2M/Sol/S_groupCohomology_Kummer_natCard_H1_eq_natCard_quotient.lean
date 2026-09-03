import Mathlib
import Definitions.Def_GroupCohomology_Kummer
import Theorems.Thm_groupCohomology_Kummer_ker_kummerHom
import Theorems.Thm_groupCohomology_Kummer_kummerHom_surjective
import P2M.Util
namespace P2MW.S_groupCohomology_Kummer_natCard_H1_eq_natCard_quotient

set_option autoImplicit false

universe u v

open groupCohomology groupCohomology.Kummer

theorem solution
    {K L : Type} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L] (p : ℕ) :
    Nat.card (H1 (kummerRep K L p))
      = Nat.card (powerSubgroup K L p ⧸
          ((powMonoidHom p : Kˣ →* Kˣ).range).subgroupOf (powerSubgroup K L p)) := by

  let e : (powerSubgroup K L p ⧸
        ((powMonoidHom p : Kˣ →* Kˣ).range).subgroupOf (powerSubgroup K L p))
      ≃* Multiplicative (H1 (kummerRep K L p)) :=
    (QuotientGroup.quotientMulEquivOfEq (ker_kummerHom (K := K) (L := L) p).symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective _ (kummerHom_surjective p))
  exact ((Nat.card_congr e.toEquiv).trans (Nat.card_congr Multiplicative.toAdd)).symm
