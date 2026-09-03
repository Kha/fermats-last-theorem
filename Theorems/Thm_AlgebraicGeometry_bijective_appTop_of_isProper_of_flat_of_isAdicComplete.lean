import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_bijective_appTop_of_isProper_of_flat_of_isAdicComplete

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

theorem AlgebraicGeometry.bijective_appTop_of_isProper_of_flat_of_isAdicComplete
    {X : Scheme.{u}} {A : CommRingCat.{u}} [IsNoetherianRing A] [IsLocalRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (p : X ⟶ Spec A) [IsProper p] [Flat p]
    (h : Function.Bijective (pullback.snd p (Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A))))).appTop) :
    Function.Bijective p.appTop := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_bijective_appTop_of_isProper_of_flat_of_isAdicComplete.solution
