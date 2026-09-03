import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Theorems.Thm_WeierstrassProjModel_exists_thirdLaw_nineCoverage_of_isElliptic_of_isDomain
import Theorems.Thm_WeierstrassProjModel_relativeGroupLaw_nonempty_of_thirdLaw_nineCoverage
import P2M.Util
namespace P2MW.S_WeierstrassProjModel_relativeGroupLaw_nonempty_of_isElliptic_of_baseChangeIso_of_isNoetherianRing
attribute [-simp] WeierstrassProjModel.kw_lrThird_substHom_X

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra WeierstrassProjModel
open MvPolynomial WeierstrassCurve HomogeneousLocalization
open scoped TensorProduct

universe u

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] WeierstrassProjModel.kw_pbac_awayAlgebra

theorem solution
    {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    (V : WeierstrassCurve.Projective R)
    [V.toAffine.IsElliptic]
    (hbc : ∀ (K : Type u) [Field K] [Algebra R K],
        Nonempty (pullback (projModelStrCR V)
            (Spec.map (CommRingCat.ofHom (algebraMap R K)))
          ≅ projModelCR (V.baseChange K))) :
    Nonempty (RelativeGroupLaw R (projModelStrCR V)) := by
  clear hbc
  obtain ⟨u₃, toE₃, hcov₉, hcompat₃⟩ :=
    WeierstrassProjModel.exists_thirdLaw_nineCoverage_of_isElliptic_of_isDomain V.toAffine
  exact WeierstrassProjModel.relativeGroupLaw_nonempty_of_thirdLaw_nineCoverage
    V.toAffine u₃ toE₃ hcov₉ hcompat₃
