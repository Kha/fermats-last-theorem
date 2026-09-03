import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCoverKaehler
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_isPrime_span_germ_and_ne_zero_of_isIntegral_fibre_of_smoothOfRelativeDimension_one

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

theorem AlgebraicGeometry.isPrime_span_germ_and_ne_zero_of_isIntegral_fibre_of_smoothOfRelativeDimension_one
    {R : Type u} [CommRing R] [IsDomain R] (ϖ : R) (hϖ : ϖ ≠ 0)
    (hmax : (Ideal.span {ϖ} : Ideal R).IsMaximal)
    {κ : Type u} [Field κ] (q : R →+* κ) (hker : RingHom.ker q = Ideal.span {ϖ})
    {X : Scheme.{u}} (c : X ⟶ Spec (.of R)) [IsIntegral X] [SmoothOfRelativeDimension 1 c]
    [IsIntegral (Limits.pullback c (Spec.map (CommRingCat.ofHom q)))]
    (x : X) (hx : x ∈ Set.range (Limits.pullback.fst c (Spec.map (CommRingCat.ofHom q))).base) :
    (Ideal.span {(X.presheaf.germ ⊤ x trivial).hom (c.appTop.hom
        ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom ϖ))}).IsPrime ∧
      (X.presheaf.germ ⊤ x trivial).hom (c.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom ϖ)) ≠ 0 := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_isPrime_span_germ_and_ne_zero_of_isIntegral_fibre_of_smoothOfRelativeDimension_one.solution
