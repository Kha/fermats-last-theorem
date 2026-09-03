import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_isReduced_sections_quotient_of_isReduced_pullback

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

theorem AlgebraicGeometry.isReduced_sections_quotient_of_isReduced_pullback
    {R : Type u} [CommRing R] {κ : Type u} [Field κ] (φ : R →+* κ) (ϖ : R)
    (hϖ : φ ϖ = 0) (hmax : (Ideal.span {ϖ}).IsMaximal)
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [IsReduced (pullback f (Spec.map (CommRingCat.ofHom φ)))]
    (V : X.Opens) (hV : IsAffineOpen V) :
    letI := ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appLE ⊤ V le_top).hom.toAlgebra
    _root_.IsReduced (Γ(X, V) ⧸ Ideal.span {algebraMap R Γ(X, V) ϖ}) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_isReduced_sections_quotient_of_isReduced_pullback.solution
