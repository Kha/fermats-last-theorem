import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_moduleFinite_globalSections_of_isProper_of_isAffineHom
set_option Elab.async false
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

theorem AlgebraicGeometry.moduleFinite_globalSections_of_isProper_of_isAffineHom
    {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    [IsProper f] [IsAffineHom f] :
    letI : Algebra R Γ(X, ⊤) := ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appTop).hom.toAlgebra
    Module.Finite R Γ(X, ⊤) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_moduleFinite_globalSections_of_isProper_of_isAffineHom.solution
