import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_SquareZeroDeformation
import Definitions.Def_Algebra_PointDerivations
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_snd_appLE_mul_tangentPoints_eq_add

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GoodReductionJacobian Scheme.TwoAffineOpenCover

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.snd_appLE_mul_tangentPoints_eq_add
    {K : Type u} [Field K] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of K)) (L : RelativeGroupLaw K f)
    (V : Type u) [AddCommGroup V] [Module K V] [Module Kᵐᵒᵖ V] [IsCentralScalar K V]
    (v₁ v₂ : TangentPoints f (L.one (𝟙 _)).1 V)
    (W : A.Opens) (a : Γ(A, W))
    (h₁ : ⊤ ≤ v₁.1 ⁻¹ᵁ W) (h₂ : ⊤ ≤ v₂.1 ⁻¹ᵁ W)
    (hμ : ⊤ ≤ (L.mul (SquareZero.toBase K V) ⟨v₁.1, v₁.2.1⟩ ⟨v₂.1, v₂.2.1⟩).1 ⁻¹ᵁ W) :
    (((L.mul (SquareZero.toBase K V) ⟨v₁.1, v₁.2.1⟩ ⟨v₂.1, v₂.2.1⟩).1.appLE W ⊤ hμ ≫
        (Scheme.ΓSpecIso (CommRingCat.of (TrivSqZeroExt K V))).hom).hom a).snd =
      ((v₁.1.appLE W ⊤ h₁ ≫ (Scheme.ΓSpecIso (CommRingCat.of (TrivSqZeroExt K V))).hom).hom a).snd +
      ((v₂.1.appLE W ⊤ h₂ ≫ (Scheme.ΓSpecIso (CommRingCat.of (TrivSqZeroExt K V))).hom).hom a).snd := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_snd_appLE_mul_tangentPoints_eq_add.solution
