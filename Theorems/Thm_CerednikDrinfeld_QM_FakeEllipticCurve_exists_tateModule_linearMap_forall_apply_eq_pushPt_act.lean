import Mathlib
import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_CerednikDrinfeld_QMCanonicalPol
import Definitions.Def_AlgebraicGeometry_PolarisationPicZero
import Definitions.Def_AlgebraicGeometry_ModulesTensorPowV2
import Definitions.Def_AlgebraicGeometry_RiemannForm
import Definitions.Def_EllipticCurve_TateModule
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_tateModule_linearMap_forall_apply_eq_pushPt_act

set_option autoImplicit false

open scoped TensorProduct Quaternion
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
  NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_tateModule_linearMap_forall_apply_eq_pushPt_act
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    {K : Type} [Field K] (E : FakeEllipticCurve Λ N K)
    (Ω : Type) [Field Ω] [Algebra K Ω] (ℓ : ℕ) [Fact ℓ.Prime] :
    ∃ ρ : ↥Λ → (TateModule ℓ (E.L.AlgPoints E.comm Ω) →ₗ[ℤ_[ℓ]] TateModule ℓ (E.L.AlgPoints E.comm Ω)),
      (∀ (m : ↥Λ) (v : TateModule ℓ (E.L.AlgPoints E.comm Ω)) (n : ℕ),
        RelativeGroupLaw.AlgPoints.toPoint ((ρ m v : ℕ → E.L.AlgPoints E.comm Ω) n) =
          pushPt (E.act m) (E.act_over m) (RelativeGroupLaw.AlgPoints.toPoint ((v : ℕ → E.L.AlgPoints E.comm Ω) n))) ∧
      (∀ h : (1 : ℍ[ℚ, a, b]) ∈ Λ, ρ ⟨1, h⟩ = LinearMap.id) ∧
      (∀ (m m' : ↥Λ) (h : (m : ℍ[ℚ, a, b]) * (m' : ℍ[ℚ, a, b]) ∈ Λ),
        ρ ⟨(m : ℍ[ℚ, a, b]) * (m' : ℍ[ℚ, a, b]), h⟩ = ρ m ∘ₗ ρ m') ∧
      (∀ m m' : ↥Λ, ρ (m + m') = ρ m + ρ m') := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_tateModule_linearMap_forall_apply_eq_pushPt_act.solution
