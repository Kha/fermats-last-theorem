import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_eq_of_forall_specMap_quotient_maximalIdeal_pow_comp_eq_of_isSchemeTheoreticallyDominant

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.eq_of_forall_specMap_quotient_maximalIdeal_pow_comp_eq_of_isSchemeTheoreticallyDominant
    {X Y Z : Scheme.{u}} [IsLocallyNoetherian X]
    (hX : ∀ U : X.Opens, (U : Set X).Nonempty → IsSchemeTheoreticallyDominant U.ι)
    (f g : X ⟶ Y) (s : Y ⟶ Z) [IsSeparated s] (hs : f ≫ s = g ≫ s) (x : X)
    (h : ∀ n : ℕ,
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
          (IsLocalRing.maximalIdeal (X.presheaf.stalk x) ^ n))) ≫ X.fromSpecStalk x ≫ f =
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
          (IsLocalRing.maximalIdeal (X.presheaf.stalk x) ^ n))) ≫ X.fromSpecStalk x ≫ g) :
    f = g := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_eq_of_forall_specMap_quotient_maximalIdeal_pow_comp_eq_of_isSchemeTheoreticallyDominant.solution
