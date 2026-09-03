import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_Opens_isProper_toSpecPolynomial_of_maximal

universe u

open CategoryTheory AlgebraicGeometry Polynomial

theorem AlgebraicGeometry.Scheme.Opens.isProper_toSpecPolynomial_of_maximal
    {k : Type u} [Field k] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k))
    [IsIntegral C] [IsProper c] (hval : ∀ x : C, ValuationRing (C.presheaf.stalk x))
    (U : C.Opens) [Nonempty U] (s : Γ(C, U))
    (hU : ∀ x : C, C.germToFunctionField U s ∈
      (algebraMap (C.presheaf.stalk x) C.functionField).range → x ∈ U) :
    IsProper ((U : Scheme.{u}).toSpecΓ ≫ Spec.map (CommRingCat.ofHom
      (Polynomial.eval₂RingHom ((U.ι ≫ c).appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom)
        (U.topIso.inv s)))) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Opens_isProper_toSpecPolynomial_of_maximal.solution
