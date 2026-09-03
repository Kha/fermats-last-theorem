import Mathlib
import Definitions.Def_AdicCompletionLocalRing
import Theorems.Thm_AdicCompletion_isNoetherianRing_of_isNoetherianRing
import Theorems.Thm_IsRegularLocalRing_isDomain
import Theorems.Thm_IsRegularLocalRing_uniqueFactorizationMonoid_of_ringKrullDim_le_two
import Theorems.Thm_IsLocalRing_ringKrullDim_adicCompletion_maximalIdeal_eq
import P2M.Util
namespace P2MW.S_IsRegularLocalRing_isDomain_and_isIntegrallyClosed_adicCompletion_of_ringKrullDim_eq_two

set_option autoImplicit false

open IsLocalRing

theorem solution (O : Type) [CommRing O] [IsRegularLocalRing O] (hdimO : ringKrullDim O = 2) :
    IsDomain (AdicCompletion (maximalIdeal O) O) ∧ IsIntegrallyClosed (AdicCompletion (maximalIdeal O) O) ∧
      IsNoetherianRing (AdicCompletion (maximalIdeal O) O) ∧ ringKrullDim (AdicCompletion (maximalIdeal O) O) = 2 := by
  classical
  haveI hno : IsNoetherianRing (AdicCompletion (maximalIdeal O) O) :=
    AdicCompletion.isNoetherianRing_of_isNoetherianRing (maximalIdeal O)
  have hdim : ringKrullDim (AdicCompletion (maximalIdeal O) O) = 2 := by
    rw [IsLocalRing.ringKrullDim_adicCompletion_maximalIdeal_eq O, hdimO]

  haveI hreg : IsRegularLocalRing (AdicCompletion (maximalIdeal O) O) := by
    refine IsRegularLocalRing.of_spanFinrank_maximalIdeal_le _ ?_
    rw [AdicCompletion.maximalIdeal_eq_map, hdim]
    have h1 := Ideal.spanFinrank_map_le_of_fg (algebraMap O (AdicCompletion (maximalIdeal O) O))
      (I := maximalIdeal O) (IsNoetherian.noetherian _)
    have h2 : ((maximalIdeal O).spanFinrank : WithBot ℕ∞) = 2 := by
      rw [IsRegularLocalRing.spanFinrank_maximalIdeal, hdimO]
    have h3 : (((maximalIdeal O).map (algebraMap O (AdicCompletion (maximalIdeal O) O))).spanFinrank : WithBot ℕ∞) ≤
        ((maximalIdeal O).spanFinrank : WithBot ℕ∞) := by exact_mod_cast h1
    exact h3.trans h2.le
  haveI hdom : IsDomain (AdicCompletion (maximalIdeal O) O) := IsRegularLocalRing.isDomain _
  haveI : UniqueFactorizationMonoid (AdicCompletion (maximalIdeal O) O) :=
    IsRegularLocalRing.uniqueFactorizationMonoid_of_ringKrullDim_le_two _ hdim.le
  exact ⟨hdom, inferInstance, hno, hdim⟩
