import Mathlib
import Definitions.Def_AlgebraicCurve_CurveModel
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_Opens_finite_preimage_singleton_toSpecPolynomial

universe u

open CategoryTheory AlgebraicGeometry Polynomial

theorem AlgebraicGeometry.Scheme.Opens.finite_preimage_singleton_toSpecPolynomial
    {k : Type u} [Field k] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k))
    [IsIntegral C] [SmoothOfRelativeDimension 1 c] [QuasiCompact c]
    (U : C.Opens) [Nonempty U] (s : Γ(C, U))
    (hs : letI := (AlgebraicCurve.baseToFunctionField c).toAlgebra
      Transcendental k (C.germToFunctionField U s))
    (p : Spec (CommRingCat.of k[X])) :
    (((U : Scheme.{u}).toSpecΓ ≫ Spec.map (CommRingCat.ofHom
      (Polynomial.eval₂RingHom ((U.ι ≫ c).appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom)
        (U.topIso.inv s)))).base ⁻¹' {p}).Finite := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Opens_finite_preimage_singleton_toSpecPolynomial.solution
