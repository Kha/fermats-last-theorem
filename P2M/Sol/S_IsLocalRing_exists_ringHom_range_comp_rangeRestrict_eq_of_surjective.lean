import Mathlib
import P2M.Util
namespace P2MW.S_IsLocalRing_exists_ringHom_range_comp_rangeRestrict_eq_of_surjective

set_option autoImplicit false

theorem solution
    {R : Type*} [CommRing R] [IsLocalRing R]
    {k : Type*} [Field k] (π : R →+* k) (hπ : Function.Surjective π)
    {K : Type*} [Field K] (φ : R →+* K) :
    ∃ ρ : φ.range →+* k, ∀ r : R, ρ (φ.rangeRestrict r) = π r := by
  have hker : RingHom.ker φ ≤ RingHom.ker π := by
    have hmax : (RingHom.ker π).IsMaximal := RingHom.ker_isMaximal_of_surjective π hπ
    rw [IsLocalRing.eq_maximalIdeal hmax]
    exact IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top φ)
  have hsurj : Function.Surjective φ.rangeRestrict := φ.rangeRestrict_surjective
  refine ⟨φ.rangeRestrict.liftOfRightInverse (Function.surjInv hsurj)
      (Function.rightInverse_surjInv hsurj) ⟨π, ?_⟩, fun r => ?_⟩
  · intro x hx
    apply hker
    rw [RingHom.mem_ker] at hx ⊢
    have := congrArg Subtype.val hx
    simpa using this
  · exact RingHom.liftOfRightInverse_comp_apply _ _ _ _ r
