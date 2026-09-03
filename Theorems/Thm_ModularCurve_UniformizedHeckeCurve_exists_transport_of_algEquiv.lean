import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_CerednikDrinfeld_QMModuliProps
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_AlgebraicCurve_Correspondence
import P2M.Util
import P2M.Sol.S_ModularCurve_UniformizedHeckeCurve_exists_transport_of_algEquiv

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsDedekindDomain AlgebraicCurve QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion TensorProduct NumberField MatrixGroups Topology

theorem ModularCurve.UniformizedHeckeCurve.exists_transport_of_algEquiv
    (Γ : Subgroup (GL (Fin 2) ℝ)) {Fc Fc' : Type} [Field Fc] [Algebra ℂ Fc] [Field Fc'] [Algebra ℂ Fc']
    (e : Fc ≃ₐ[ℂ] Fc') (U : ModularCurve.UniformizedHeckeCurve Γ Fc) :
    let pm : Place ℂ Fc → Place ℂ Fc' := fun P =>
      P.restrictAlong (e.symm : Fc' →ₐ[ℂ] Fc) ((e.symm : Fc' →ₐ[ℂ] Fc).toRingHom.isIntegral_of_surjective e.symm.surjective)
    ∃ U' : ModularCurve.UniformizedHeckeCurve Γ Fc',
      (∀ τ : UpperHalfPlane, U'.pt τ = pm (U.pt τ)) ∧
      (∀ (x : Fc') (τ : UpperHalfPlane), U'.realize x τ = U.realize (e.symm x) τ) ∧
      (∀ τ : UpperHalfPlane, U'.ramification τ = U.ramification τ) ∧
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime), U'.heckePoints ℓ hℓ = U.heckePoints ℓ hℓ) ∧
      U'.distinguished = e U.distinguished ∧
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (D : Divisor ℂ Fc),
        U'.corr ℓ hℓ (Finsupp.mapDomain pm D) = Finsupp.mapDomain pm (U.corr ℓ hℓ D)) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_UniformizedHeckeCurve_exists_transport_of_algEquiv.solution
