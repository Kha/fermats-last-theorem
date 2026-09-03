import Mathlib
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_WeierstrassCurve_DrinfeldBasisRelative
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_DrinfeldGlobal_comap_torsionIdealOver_eq_torsionIdeal
attribute [-instance] WeierstrassProjModel.quotGradingSubmoduleDegreeZeroFiniteType WeierstrassProjModel.kw_lrChart_tensorCommRing WeierstrassProjModel.kw_lrChart_biGrading_gradedAlgebra WeierstrassProjModel.projModel_isIso_spec_mapCR WeierstrassProjModel.kw_lrSymOC_isDomain_ℬ₀ WeierstrassProjModel.isProper_projModelStrCR WeierstrassProjModel.homogeneousSubmoduleDegreeZeroFiniteType
attribute [-simp] WeierstrassProjModel.kw_lrAdd_substHom_X WeierstrassProjModel.kw_lrSym_substHom_X

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra WeierstrassProjModel
  WeierstrassCurve.DrinfeldGlobal

attribute [local instance] MvPolynomial.gradedAlgebra

theorem WeierstrassCurve.DrinfeldGlobal.comap_torsionIdealOver_eq_torsionIdeal
    {B T : Type u} [CommRing B] [CommRing T] (W : WeierstrassCurve.Projective B) (f : B →+* T)
    (φc : projModelGradingCR W →+*ᵍ projModelGradingCR (W.map f))
    (hφc : HomogeneousIdeal.irrelevant (projModelGradingCR (W.map f)) ≤
      (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φc)
    (hcoef : IsCoefficientHom W f φc)
    (hsq : Proj.map φc hφc ≫ projModelStrCR W =
      projModelStrCR (W.map f) ≫ Spec.map (CommRingCat.ofHom f))
    (G : RelativeGroupLaw B (projModelStrCR W)) (L : RelativeGroupLaw T (projModelStrCR (W.map f)))
    (hmul : ∀ {S : Scheme.{u}} (s : S ⟶ Spec (CommRingCat.of T))
      (x y : SchemeHomOver s (projModelStrCR (W.map f))),
      (L.mul s x y).1 ≫ Proj.map φc hφc =
        (G.mul (s ≫ Spec.map (CommRingCat.ofHom f))
          ⟨x.1 ≫ Proj.map φc hφc, by rw [Category.assoc, hsq, ← Category.assoc, x.2]⟩
          ⟨y.1 ≫ Proj.map φc hφc, by rw [Category.assoc, hsq, ← Category.assoc, y.2]⟩).1)
    (hone : (L.one (𝟙 (Spec (CommRingCat.of T)))).1 ≫ Proj.map φc hφc =
      Spec.map (CommRingCat.ofHom f) ≫ (G.one (𝟙 (Spec (CommRingCat.of B)))).1)
    (q : ℕ) :
    (G.torsionIdealOver q (Spec.map (CommRingCat.ofHom f))).comap
      (pullback.lift (pullback.fst (projModelStrCR (W.map f)) (𝟙 _) ≫ Proj.map φc hφc)
        (pullback.snd (projModelStrCR (W.map f)) (𝟙 _))
        (by rw [Category.assoc, hsq, ← Category.assoc, pullback.condition, Category.assoc, Category.id_comp])) =
      torsionIdeal L q := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_DrinfeldGlobal_comap_torsionIdealOver_eq_torsionIdeal.solution
