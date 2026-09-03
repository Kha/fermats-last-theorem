import Mathlib
import Definitions.Def_AlgebraicGeometry_SquareZeroDeformation
import Definitions.Def_AlgebraicGeometry_SquareZeroRelTangent
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_RelTangentPoints_existsUnique_comp_openInclusion_eq

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u
theorem AlgebraicGeometry.RelTangentPoints.existsUnique_comp_openInclusion_eq
    {k : Type u} [Field k] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of k))
    (pt : Spec (CommRingCat.of k) ⟶ X)
    (V : Type u) [AddCommGroup V] [Module k V] [Module kᵐᵒᵖ V] [IsCentralScalar k V]
    {Z₀ Z : Scheme.{u}} (f₀ : Z₀ ⟶ Spec (CommRingCat.of k))
    (q₁ : Z ⟶ Z₀) (q₂ : Z ⟶ SquareZero.spec k V) (hZ : IsPullback q₁ q₂ f₀ (SquareZero.toBase k V))
    (w : RelTangentPoints x pt V f₀ q₁ q₂ hZ)
    (U : X.Opens) (p₁ : Spec (CommRingCat.of k) ⟶ (U : Scheme.{u})) (hp₁ : p₁ ≫ U.ι = pt) :
    ∃! w₁ : Z ⟶ (U : Scheme.{u}), w₁ ≫ U.ι = w.1 := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_RelTangentPoints_existsUnique_comp_openInclusion_eq.solution
