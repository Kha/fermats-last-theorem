import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Point
import Mathlib.RingTheory.Localization.FractionRing
import Theorems.Thm_WeierstrassProjModel_isDomain_chartTensor_of_isElliptic
import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import P2M.Util
import P2M.Sol.S_WeierstrassProjModel_kw_lr_chartTensor_genericProj_pointClass_ne

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra WeierstrassProjModel
open MvPolynomial WeierstrassCurve HomogeneousLocalization
open scoped TensorProduct

universe u

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] WeierstrassProjModel.kw_pbac_awayAlgebra

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

set_option quotPrecheck false in
local notation "𝒜" i => HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
  (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
    (X i : MvPolynomial (Fin 3) R))
attribute [local instance] MvPolynomial.gradedAlgebra WeierstrassProjModel.kw_pbac_awayAlgebra in
theorem WeierstrassProjModel.kw_lr_chartTensor_genericProj_pointClass_ne
    [IsDomain R] [IsNoetherianRing R] [W.IsElliptic] (i j : Fin 3) :
    haveI : IsDomain ((𝒜 i) ⊗[R] (𝒜 j)) := isDomain_chartTensor_of_isElliptic W i j
    let ψᵢ : (𝒜 i) →ₐ[R] FractionRing ((𝒜 i) ⊗[R] (𝒜 j)) :=
      (IsScalarTower.toAlgHom R ((𝒜 i) ⊗[R] (𝒜 j)) (FractionRing ((𝒜 i) ⊗[R] (𝒜 j)))).comp
        Algebra.TensorProduct.includeLeft
    let ψⱼ : (𝒜 j) →ₐ[R] FractionRing ((𝒜 i) ⊗[R] (𝒜 j)) :=
      (IsScalarTower.toAlgHom R ((𝒜 i) ⊗[R] (𝒜 j)) (FractionRing ((𝒜 i) ⊗[R] (𝒜 j)))).comp
        Algebra.TensorProduct.includeRight
    (⟦kw_lrApt_chartEval W (FractionRing ((𝒜 i) ⊗[R] (𝒜 j))) i ψᵢ⟧
        : WeierstrassCurve.Projective.PointClass (FractionRing ((𝒜 i) ⊗[R] (𝒜 j))))
      ≠ ⟦kw_lrApt_chartEval W (FractionRing ((𝒜 i) ⊗[R] (𝒜 j))) j ψⱼ⟧ := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassProjModel_kw_lr_chartTensor_genericProj_pointClass_ne.solution
