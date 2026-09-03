import Mathlib
import Definitions.Def_MvPolynomial_CrossingResolution
import P2M.Util
namespace P2MW.S_MvPolynomial_CrossingQuotient_existsUnique_ringHom_comp_algebraMap_eq_and_apply_U_eq_and_apply_V_eq

set_option autoImplicit false

open MvPolynomial

theorem solution
    {W : Type*} [CommRing W] {S : Type*} [CommRing S] (ι : W →+* S) (t : W) (x y : S)
    (hxy : x * y = ι t) :
    ∃! χ : CrossingQuotient W t →+* S,
      χ.comp (algebraMap W (CrossingQuotient W t)) = ι ∧ χ (CrossingQuotient.U t) = x ∧ χ (CrossingQuotient.V t) = y := by
  letI : Algebra W S := ι.toAlgebra
  have hxy' : x * y = algebraMap W S t := hxy
  refine ⟨(CrossingQuotient.lift t x y hxy').toRingHom, ⟨?_, ?_, ?_⟩, ?_⟩
  · exact (CrossingQuotient.lift t x y hxy').comp_algebraMap
  · exact CrossingQuotient.lift_U t x y hxy'
  · exact CrossingQuotient.lift_V t x y hxy'
  · rintro χ ⟨hχ, hU, hV⟩
    apply Ideal.Quotient.ringHom_ext
    apply MvPolynomial.ringHom_ext
    · intro w
      have e1 : (Ideal.Quotient.mk (Ideal.span {(X 0 * X 1 - C t : MvPolynomial (Fin 2) W)}) (C w)
          : CrossingQuotient W t) = algebraMap W (CrossingQuotient W t) w := rfl
      rw [RingHom.comp_apply, RingHom.comp_apply, e1, ← RingHom.comp_apply χ, hχ]
      change ι w = CrossingQuotient.lift t x y hxy' (algebraMap W (CrossingQuotient W t) w)
      rw [AlgHom.commutes]
      rfl
    · intro i
      fin_cases i
      · change χ (CrossingQuotient.U t) = CrossingQuotient.lift t x y hxy' (CrossingQuotient.U t)
        rw [hU, CrossingQuotient.lift_U]
      · change χ (CrossingQuotient.V t) = CrossingQuotient.lift t x y hxy' (CrossingQuotient.V t)
        rw [hV, CrossingQuotient.lift_V]
