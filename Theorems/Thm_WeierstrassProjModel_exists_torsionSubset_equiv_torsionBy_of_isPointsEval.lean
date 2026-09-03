import Definitions.Def_WeierstrassCurve_ProjModel
import Mathlib.Algebra.Module.Torsion.Basic
import P2M.Util
import P2M.Sol.S_WeierstrassProjModel_exists_torsionSubset_equiv_torsionBy_of_isPointsEval

open AlgebraicGeometry CategoryTheory NeronModelInfra WeierstrassProjModel

universe u

theorem WeierstrassProjModel.exists_torsionSubset_equiv_torsionBy_of_isPointsEval
    {R : Type u} [CommRing R] (V : WeierstrassCurve.Projective R)
    (G : RelativeGroupLaw R (projModelStrCR V))
    (ev : ∀ (F : Type u) [Field F] [DecidableEq F] [Algebra R F],
      SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R F))) (projModelStrCR V) ≃
        (V.baseChange F).toAffine.Point)
    (hev : IsPointsEval V G ev)
    (F : Type u) [Field F] [DecidableEq F] [Algebra R F] (d : ℕ) :
    ∃ e : ↥(G.torsionSubset (Spec.map (CommRingCat.ofHom (algebraMap R F))) d) ≃
        ↥(Submodule.torsionBy ℤ (V.baseChange F).toAffine.Point (d : ℤ)),
      (∀ x : ↥(G.torsionSubset (Spec.map (CommRingCat.ofHom (algebraMap R F))) d),
          (e x : (V.baseChange F).toAffine.Point) = ev F x.1) ∧
      (∀ (x y : ↥(G.torsionSubset (Spec.map (CommRingCat.ofHom (algebraMap R F))) d))
          (hxy : G.mul (Spec.map (CommRingCat.ofHom (algebraMap R F))) x.1 y.1 ∈
            G.torsionSubset (Spec.map (CommRingCat.ofHom (algebraMap R F))) d),
          e ⟨_, hxy⟩ = e x + e y) ∧
      (∀ (σ : F ≃ₐ[R] F)
          (x : ↥(G.torsionSubset (Spec.map (CommRingCat.ofHom (algebraMap R F))) d))
          (hσx : galTwist σ x.1 ∈
            G.torsionSubset (Spec.map (CommRingCat.ofHom (algebraMap R F))) d),
          (e ⟨_, hσx⟩ : (V.baseChange F).toAffine.Point) =
            WeierstrassCurve.Affine.Point.map (σ : F →ₐ[R] F)
              (e x : (V.baseChange F).toAffine.Point)) := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassProjModel_exists_torsionSubset_equiv_torsionBy_of_isPointsEval.solution
