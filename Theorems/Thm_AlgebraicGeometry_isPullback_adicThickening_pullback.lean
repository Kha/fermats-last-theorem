import Mathlib
import Definitions.Def_AlgebraicGeometry_AdicThickening
import Definitions.Def_AlgebraicGeometry_ProjSpace
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_isPullback_adicThickening_pullback

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.isPullback_adicThickening_pullback
    {R : Type u} [CommRing R] (I : Ideal R) {X Y : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) (g : Y ⟶ Spec (CommRingCat.of R)) (n : ℕ)
    (prX : adicThickening (pullback.fst f g ≫ f) I n ⟶ adicThickening f I n)
    (hprX₁ : prX ≫ adicThickeningι f I n = adicThickeningι (pullback.fst f g ≫ f) I n ≫ pullback.fst f g)
    (hprX₂ : prX ≫ adicThickeningToBase f I n = adicThickeningToBase (pullback.fst f g ≫ f) I n)
    (prY : adicThickening (pullback.fst f g ≫ f) I n ⟶ adicThickening g I n)
    (hprY₁ : prY ≫ adicThickeningι g I n = adicThickeningι (pullback.fst f g ≫ f) I n ≫ pullback.snd f g)
    (hprY₂ : prY ≫ adicThickeningToBase g I n = adicThickeningToBase (pullback.fst f g ≫ f) I n) :
    IsPullback prX prY (adicThickeningToBase f I n) (adicThickeningToBase g I n) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_isPullback_adicThickening_pullback.solution
