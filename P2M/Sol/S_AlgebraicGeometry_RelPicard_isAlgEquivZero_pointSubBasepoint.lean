import Mathlib
import Definitions.Def_AlgebraicGeometry_RelPicardAbelJacobiFamily
import Theorems.Thm_AlgebraicGeometry_RelPicard_nonempty_ajFamily_fibre_iso
import Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_isInvertible_I
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_RelPicard_isAlgEquivZero_pointSubBasepoint

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian"

theorem solution
    {k : Type u} [Field k] {A : Scheme.{u}} {a : A ⟶ Spec (CommRingCat.of k)}
    [IsSeparated a] [SmoothOfRelativeDimension 1 a] [GeometricallyIntegral a] [LocallyOfFiniteType a]
    (P ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) a) :
    IsAlgEquivZero a ((Scheme.Modules.pullback (toProdSpec a)).obj (pointSubBasepointModule (a := a) P ε)) :=
  by
  refine ⟨A, a, inferInstance, inferInstance, ajFamily (a := a) ε, isInvertible_ajFamily (a := a) ε, ε, P, ?_, ?_⟩
  · obtain ⟨i⟩ := nonempty_ajFamily_fibre_iso (a := a) ε ε
    obtain ⟨p⟩ := Scheme.IdealSheafData.IsInvertible.nonempty_invModule_tensor_module_iso
      (RelEffCartierDiv.isInvertible_I (RelEffCartierDiv.ofPoint a ε.1 ε.2))
    exact ⟨i ≪≫ p⟩
  · obtain ⟨i⟩ := nonempty_ajFamily_fibre_iso (a := a) ε P
    exact ⟨i ≪≫ (fstPullbackToProdSpecPullbackIso a _).symm⟩
