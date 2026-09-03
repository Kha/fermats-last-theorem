import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_FLTPrelim_GaloisRep
import P2M.Util
import P2M.Sol.S_WeierstrassProjModel_exists_torsionSubset_equiv_torsionBy_galoisEquivariant

open AlgebraicGeometry CategoryTheory NeronModelInfra WeierstrassProjModel
open WeierstrassCurve
open scoped WeierstrassCurve.Affine

theorem WeierstrassProjModel.exists_torsionSubset_equiv_torsionBy_galoisEquivariant
    (W : WeierstrassCurve ℤ) (p : ℕ)
    (G : RelativeGroupLaw (GaloisRep.ratLocalizedAt p)
      (projModelStrCR (W.map (algebraMap ℤ (GaloisRep.ratLocalizedAt p))).toProjective))
    (ev : ∀ (F : Type) [Field F] [DecidableEq F] [Algebra (GaloisRep.ratLocalizedAt p) F],
      SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap (GaloisRep.ratLocalizedAt p) F)))
          (projModelStrCR (W.map (algebraMap ℤ (GaloisRep.ratLocalizedAt p))).toProjective) ≃
        ((W.map (algebraMap ℤ (GaloisRep.ratLocalizedAt p))).toProjective.baseChange
            F).toAffine.Point)
    (hev : IsPointsEval (W.map (algebraMap ℤ (GaloisRep.ratLocalizedAt p))).toProjective G ev)
    (d : ℕ) :
    ∃ e : ↥(G.torsionSubset (Spec.map (CommRingCat.ofHom
              (algebraMap (GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ)))) d) ≃
        ↥(Submodule.torsionBy ℤ
            ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point (d : ℤ)),
      (∀ (x y : ↥(G.torsionSubset (Spec.map (CommRingCat.ofHom
              (algebraMap (GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ)))) d))
          (hxy : G.mul (Spec.map (CommRingCat.ofHom
              (algebraMap (GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ)))) x.1 y.1 ∈
            G.torsionSubset (Spec.map (CommRingCat.ofHom
              (algebraMap (GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ)))) d),
          e ⟨_, hxy⟩ = e x + e y) ∧
      ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
        (x : ↥(G.torsionSubset (Spec.map (CommRingCat.ofHom
              (algebraMap (GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ)))) d))
        (hx : galTwist (σ.restrictScalars (GaloisRep.ratLocalizedAt p)) x.1 ∈
            G.torsionSubset (Spec.map (CommRingCat.ofHom
              (algebraMap (GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ)))) d),
        e ⟨_, hx⟩ = σ • e x := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassProjModel_exists_torsionSubset_equiv_torsionBy_galoisEquivariant.solution
