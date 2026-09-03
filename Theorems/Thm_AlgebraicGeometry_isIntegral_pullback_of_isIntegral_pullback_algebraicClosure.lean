import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_isIntegral_pullback_of_isIntegral_pullback_algebraicClosure

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section
set_option autoImplicit false

theorem AlgebraicGeometry.isIntegral_pullback_of_isIntegral_pullback_algebraicClosure
    {R : Type} [CommRing R] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of R))
    (K : Type) [Field K] [Algebra R K]
    (h : IsIntegral ↑(pullback f (Spec.map (CommRingCat.ofHom
      ((algebraMap K (AlgebraicClosure K)).comp (algebraMap R K)))))) :
    IsIntegral ↑(pullback f (Spec.map (CommRingCat.ofHom (algebraMap R K)))) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_isIntegral_pullback_of_isIntegral_pullback_algebraicClosure.solution
