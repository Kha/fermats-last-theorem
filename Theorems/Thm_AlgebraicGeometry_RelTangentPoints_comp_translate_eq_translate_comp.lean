import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_SquareZeroDeformation
import Definitions.Def_AlgebraicGeometry_SquareZeroRelTangent
import Definitions.Def_AlgebraicGeometry_TangentCoordsOfPair
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_RelTangentPoints_comp_translate_eq_translate_comp

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GoodReductionJacobian NeronModelInfra

universe u
theorem AlgebraicGeometry.RelTangentPoints.comp_translate_eq_translate_comp
    {k : Type u} [Field k] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of k)) (L : RelativeGroupLaw k x)
    (V : Type u) [AddCommGroup V] [Module k V] [Module kᵐᵒᵖ V] [IsCentralScalar k V]
    (V' : Type u) [AddCommGroup V'] [Module k V'] [Module kᵐᵒᵖ V'] [IsCentralScalar k V']
    {Z₀ Z Z₀' Z' : Scheme.{u}} (f₀ : Z₀ ⟶ Spec (CommRingCat.of k)) (f₀' : Z₀' ⟶ Spec (CommRingCat.of k))
    (q₁ : Z ⟶ Z₀) (q₂ : Z ⟶ SquareZero.spec k V) (hZ : IsPullback q₁ q₂ f₀ (SquareZero.toBase k V))
    (q₁' : Z' ⟶ Z₀') (q₂' : Z' ⟶ SquareZero.spec k V') (hZ' : IsPullback q₁' q₂' f₀' (SquareZero.toBase k V'))
    (g₀ : Z₀ ⟶ Z₀') (hg₀f : g₀ ≫ f₀' = f₀)
    (g : Z ⟶ Z') (hg₁ : g ≫ q₁' = q₁ ≫ g₀)
    (hg₀ : SquareZero.zeroSection V f₀ q₁ q₂ hZ ≫ g = g₀ ≫ SquareZero.zeroSection V' f₀' q₁' q₂' hZ')
    (w' : Z' ⟶ X) (hw' : w' ≫ x = RelTangentPoints.base V' q₂')
    (w : Z ⟶ X) (hw : w ≫ x = RelTangentPoints.base V q₂) (hgw : g ≫ w' = w) :
    g ≫ (RelTangentPoints.translate x L V' f₀' q₁' q₂' hZ' w' hw').1 =
      (RelTangentPoints.translate x L V f₀ q₁ q₂ hZ w hw).1 := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_RelTangentPoints_comp_translate_eq_translate_comp.solution
