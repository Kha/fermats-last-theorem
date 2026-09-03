import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_isSeparated_and_quasiCompact_of_isIntegralHom_of_surjective

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory

universe u

theorem AlgebraicGeometry.Scheme.isSeparated_and_quasiCompact_of_isIntegralHom_of_surjective
    {B : Type u} [CommRing B] {M X : Scheme.{u}} (πM : M ⟶ Spec (CommRingCat.of B))
    (πX : X ⟶ Spec (CommRingCat.of B)) (π : M ⟶ X) (hπX : π ≫ πX = πM)
    (hint : IsIntegralHom π) (hsurj : Function.Surjective π.base)
    (hsep : IsSeparated πM) (hqc : QuasiCompact πM) :
    IsSeparated πX ∧ QuasiCompact πX := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_isSeparated_and_quasiCompact_of_isIntegralHom_of_surjective.solution
