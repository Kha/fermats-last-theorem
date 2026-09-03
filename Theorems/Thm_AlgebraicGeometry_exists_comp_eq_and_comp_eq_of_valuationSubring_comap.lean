import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_exists_comp_eq_and_comp_eq_of_valuationSubring_comap

open CategoryTheory AlgebraicGeometry

universe u

theorem AlgebraicGeometry.exists_comp_eq_and_comp_eq_of_valuationSubring_comap
    {Ω K' : Type u} [Field Ω] [Field K'] (φ : K' →+* Ω) (A : ValuationSubring Ω)
    {X : Scheme.{u}} (x : Spec (CommRingCat.of K') ⟶ X) (y : Spec (CommRingCat.of ↥A) ⟶ X)
    (hxy : Spec.map (CommRingCat.ofHom A.subtype) ≫ y = Spec.map (CommRingCat.ofHom φ) ≫ x) :
    ∃ z : Spec (CommRingCat.of ↥(A.comap φ)) ⟶ X,
      Spec.map (CommRingCat.ofHom (A.comap φ).subtype) ≫ z = x ∧
      Spec.map (CommRingCat.ofHom ((φ.comp (A.comap φ).subtype).codRestrict A.toSubring (fun r => r.2))) ≫ z = y := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_comp_eq_and_comp_eq_of_valuationSubring_comap.solution
