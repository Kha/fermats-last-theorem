import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
import P2M.Util
import P2M.Sol.S_WeierstrassProjModel_kw_bc_awayIsPushout_Y

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra WeierstrassProjModel
open MvPolynomial HomogeneousLocalization HomogeneousIdealQuotientGrading

attribute [local instance] MvPolynomial.gradedAlgebra

theorem WeierstrassProjModel.kw_bc_awayIsPushout_Y {R : Type} [CommRing R]
    (W : WeierstrassCurve R) (K : Type) [CommRing K] [Algebra R K] :
    let ψ : projModelGradingCR W.toProjective →+*ᵍ
        projModelGradingCR (W.map (algebraMap R K)).toProjective :=
      { toRingHom := Ideal.quotientMap _ (MvPolynomial.map (algebraMap R K)) <| by
          rw [projModelHomogeneousIdealCR_toIdeal, projModelHomogeneousIdealCR_toIdeal]
          have h : (Ideal.span {W.toProjective.polynomial}).map
                (MvPolynomial.map (algebraMap R K))
              = Ideal.span {(W.map (algebraMap R K)).toProjective.polynomial} := by
            rw [Ideal.map_span, Set.image_singleton,
              WeierstrassCurve.Projective.map_polynomial]
          rw [← h]
          exact Ideal.le_comap_map,
        map_mem := by
          rintro n _ ⟨p, hp, rfl⟩
          exact mk_mem_quotGradingSubmodule _ _
            ((mem_homogeneousSubmodule _ _).mpr
              (((mem_homogeneousSubmodule _ _).mp hp).map (algebraMap R K))) }
    IsPullback
      (Spec.map (CommRingCat.ofHom (Away.map ψ
        (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
          (X 1 : MvPolynomial (Fin 3) R)))))
      (Spec.map (CommRingCat.ofHom
        ((fromZeroRingHom (projModelGradingCR (W.map (algebraMap R K)).toProjective)
            (Submonoid.powers (ψ (Ideal.Quotient.mk _
              (X 1 : MvPolynomial (Fin 3) R))))).comp
          (algebraMap K ↥(projModelGradingCR (W.map (algebraMap R K)).toProjective 0)))))
      (Spec.map (CommRingCat.ofHom
        ((fromZeroRingHom (projModelGradingCR W.toProjective)
            (Submonoid.powers (Ideal.Quotient.mk _
              (X 1 : MvPolynomial (Fin 3) R)))).comp
          (algebraMap R ↥(projModelGradingCR W.toProjective 0)))))
      (Spec.map (CommRingCat.ofHom (algebraMap R K))) := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassProjModel_kw_bc_awayIsPushout_Y.solution
