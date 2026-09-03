import Mathlib
import Definitions.Def_CerednikDrinfeld_SchemeNilpPoints
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_exists_finite_algebra_specMap_comp_eq_of_isFinite

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.exists_finite_algebra_specMap_comp_eq_of_isFinite
    {B : Type} [CommRing B] {K : Scheme.{0}} (g : K ⟶ Spec (CommRingCat.of B)) [IsFinite g]
    (C : Type) [CommRing C] [Algebra B C] (κ : Spec (CommRingCat.of C) ⟶ K)
    (hκ : κ ≫ g = Scheme.specOver (𝒪 := B) C) :
    ∃ (D : Type) (_ : CommRing D) (_ : Algebra B D) (_ : Module.Finite B D)
      (ι : Spec (CommRingCat.of D) ⟶ K) (φ : D →ₐ[B] C),
      ι ≫ g = Scheme.specOver (𝒪 := B) D ∧ Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ ι = κ := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_finite_algebra_specMap_comp_eq_of_isFinite.solution
