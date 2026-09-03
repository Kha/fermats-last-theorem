import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_SquareZeroDeformation
import Definitions.Def_AlgebraicGeometry_SquareZeroRelTangent
import Definitions.Def_AlgebraicGeometry_TangentCoordsOfPair
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_RelTangentPoints_eq_comp_zeroSection_of_thickenedPoint_comp_eq

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem AlgebraicGeometry.RelTangentPoints.eq_comp_zeroSection_of_thickenedPoint_comp_eq
    {k : Type u} [Field k] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of k)) (L : RelativeGroupLaw k x)
    (V : Type u) [AddCommGroup V] [Module k V] [Module kᵐᵒᵖ V] [IsCentralScalar k V] [Module.Finite k V]
    {Z₀ Z : Scheme.{u}} [CompactSpace Z₀] [QuasiSeparatedSpace Z₀] (f₀ : Z₀ ⟶ Spec (CommRingCat.of k))
    (h₀ : Function.Bijective ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ f₀.appTop).hom)
    (q₁ : Z ⟶ Z₀) (q₂ : Z ⟶ SquareZero.spec k V) (hZ : IsPullback q₁ q₂ f₀ (SquareZero.toBase k V))
    (w₀ : Z ⟶ X) (hw₀ : w₀ ≫ x = q₂ ≫ SquareZero.toBase k V)
    (y : Spec (CommRingCat.of k) ⟶ Z₀)
    (yZ : SquareZero.spec k V ⟶ Z) (hyZ₁ : yZ ≫ q₁ = SquareZero.toBase k V ≫ y) (hyZ₂ : yZ ≫ q₂ = 𝟙 _)
    (hconst : yZ ≫ w₀ = SquareZero.toBase k V ≫ y ≫ SquareZero.zeroSection V f₀ q₁ q₂ hZ ≫ w₀) :
    w₀ = q₁ ≫ SquareZero.zeroSection V f₀ q₁ q₂ hZ ≫ w₀ := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_RelTangentPoints_eq_comp_zeroSection_of_thickenedPoint_comp_eq.solution
