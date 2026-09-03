import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_IdealSheafData_isFinite_and_finrank_subschemeIota_comp_eq_of_map_germ_eq_maximalIdeal

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry
theorem AlgebraicGeometry.Scheme.IdealSheafData.isFinite_and_finrank_subschemeIota_comp_eq_of_map_germ_eq_maximalIdeal
    {k : Type u} [Field k] {X : Scheme.{u}} (q : X ⟶ Spec (CommRingCat.of k))
    (K : X.IdealSheafData) {N : ℕ} (x : Fin N → X) (hx : Function.Injective x)
    (hsupp : (K.support : Set X) = Set.range x)
    (hmax : ∀ i, ∃ (U : X.affineOpens) (hU : x i ∈ (U : X.Opens)),
      Ideal.map (X.presheaf.germ (U : X.Opens) (x i) hU).hom (K.ideal U) = IsLocalRing.maximalIdeal (X.presheaf.stalk (x i)))
    (hrat : ∀ i, ∃ s : Spec (CommRingCat.of k) ⟶ X, s ≫ q = 𝟙 _ ∧ x i ∈ Set.range s.base) :
    IsFinite (K.subschemeι ≫ q) ∧ ∀ t : Spec (CommRingCat.of k), (K.subschemeι ≫ q).finrank t = N := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_isFinite_and_finrank_subschemeIota_comp_eq_of_map_germ_eq_maximalIdeal.solution
