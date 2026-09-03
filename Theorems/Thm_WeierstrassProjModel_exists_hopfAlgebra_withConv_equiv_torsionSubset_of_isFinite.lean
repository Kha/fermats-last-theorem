import Mathlib
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_WeierstrassCurve_ProjModel
import P2M.Util
import P2M.Sol.S_WeierstrassProjModel_exists_hopfAlgebra_withConv_equiv_torsionSubset_of_isFinite
attribute [-instance] WeierstrassProjModel.quotGradingSubmoduleDegreeZeroFiniteType WeierstrassProjModel.kw_lrChart_tensorCommRing WeierstrassProjModel.kw_lrChart_biGrading_gradedAlgebra WeierstrassProjModel.projModel_isIso_spec_mapCR WeierstrassProjModel.kw_lrSymOC_isDomain_ℬ₀ WeierstrassProjModel.isProper_projModelStrCR WeierstrassProjModel.homogeneousSubmoduleDegreeZeroFiniteType
attribute [-simp] WeierstrassProjModel.kw_lrAdd_substHom_X WeierstrassProjModel.kw_lrSym_substHom_X

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra WeierstrassProjModel
open scoped WeierstrassCurve.Affine in
open WeierstrassCurve WeierstrassCurve.Affine.Point in
theorem WeierstrassProjModel.exists_hopfAlgebra_withConv_equiv_torsionSubset_of_isFinite
    (K : Type) [Field K] (W : WeierstrassCurve K) [W.IsElliptic] (n : ℕ)
    (G : RelativeGroupLaw K (projModelStrCR W.toProjective))
    (ev : ∀ (F : Type) [Field F] [DecidableEq F] [Algebra K F],
      SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K F)))
          (projModelStrCR W.toProjective) ≃
        (W.toProjective.baseChange F).toAffine.Point)
    (hev : IsPointsEval W.toProjective G ev)
    (hfin : IsFinite (G.schemeKerStr n)) :
    letI : DecidableEq (AlgebraicClosure K) := Classical.decEq _
    ∃ (A : Type) (_ : CommRing A) (_ : HopfAlgebra K A),
      Module.Finite K A ∧ Coalgebra.IsCocomm K A ∧
      ∃ eH : WithConv (A →ₐ[K] AlgebraicClosure K) ≃
            ↥(G.torsionSubset (Spec.map (CommRingCat.ofHom
              (algebraMap K (AlgebraicClosure K)))) n),
        (∀ f g, (eH (f * g)).1 =
          G.mul (Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K))))
            (eH f).1 (eH g).1) ∧
        ∀ (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
          (f g : WithConv (A →ₐ[K] AlgebraicClosure K)),
          (∀ a : A, g a = σ (f a)) → (eH g).1 = galTwist σ (eH f).1 := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassProjModel_exists_hopfAlgebra_withConv_equiv_torsionSubset_of_isFinite.solution
