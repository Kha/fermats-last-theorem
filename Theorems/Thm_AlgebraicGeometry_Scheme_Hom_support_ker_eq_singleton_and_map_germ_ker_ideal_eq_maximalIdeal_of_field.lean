import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_Hom_support_ker_eq_singleton_and_map_germ_ker_ideal_eq_maximalIdeal_of_field

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing

universe u

theorem AlgebraicGeometry.Scheme.Hom.support_ker_eq_singleton_and_map_germ_ker_ideal_eq_maximalIdeal_of_field
    {K : Type u} [Field K] {C : Scheme.{u}} (σ : Spec (CommRingCat.of K) ⟶ C) [IsClosedImmersion σ] :
    ((σ.ker).support : Set ↥C) = {σ.base (IsLocalRing.closedPoint K)} ∧
    ∀ (U : C.affineOpens) (hx : σ.base (IsLocalRing.closedPoint K) ∈ (U : C.Opens)),
      Ideal.map (C.presheaf.germ (U : C.Opens) (σ.base (IsLocalRing.closedPoint K)) hx).hom (σ.ker.ideal U) =
        IsLocalRing.maximalIdeal (C.presheaf.stalk (σ.base (IsLocalRing.closedPoint K))) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Hom_support_ker_eq_singleton_and_map_germ_ker_ideal_eq_maximalIdeal_of_field.solution
