import Definitions.Def_CohCarrier_Inst
import Definitions.Def_ModularCurve_PeriodMap
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.PrincipalIdealDomain
import P2M.Util
import P2M.Sol.S_CohCarrier_exists_linearEquiv_tensorProduct_H1_tmul_eq_and_heckeTL_baseChange_and_map_parabolicHoms

set_option autoImplicit false

open scoped TensorProduct

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 800000 in

theorem CohCarrier.exists_linearEquiv_tensorProduct_H1_tmul_eq_and_heckeTL_baseChange_and_map_parabolicHoms
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsPrincipalIdealRing 𝒪]
    (F : Type) [Field F] [Algebra 𝒪 F] (hinj : Function.Injective (algebraMap 𝒪 F))
    (N : ℕ) [NeZero N] (H : Subgroup (ZMod N)ˣ) :
    ∃ Φ : F ⊗[𝒪] CohCarrier.H1 N H 𝒪 ≃ₗ[F] CohCarrier.H1 N H F,
      (∀ (x : F) (φ : CohCarrier.H1 N H 𝒪),
        Φ (x ⊗ₜ[𝒪] φ) = x • ((algebraMap 𝒪 F).toAddMonoidHom.comp φ)) ∧
      (∀ (ℓ : ℕ) [NeZero ℓ] (v : F ⊗[𝒪] CohCarrier.H1 N H 𝒪),
        Φ ((CohCarrier.heckeTL N H 𝒪 ℓ).baseChange F v) = CohCarrier.heckeTL N H F ℓ (Φ v)) ∧
      Submodule.map (Φ : F ⊗[𝒪] CohCarrier.H1 N H 𝒪 →ₗ[F] CohCarrier.H1 N H F)
          (LinearMap.range ((ModularCurve.Period.parabolicHoms 𝒪 (CohCarrier.GammaH N H) 𝒪).subtype.baseChange F)) =
        ModularCurve.Period.parabolicHoms F (CohCarrier.GammaH N H) F := by p2m_exact_reverting @_root_.P2MW.S_CohCarrier_exists_linearEquiv_tensorProduct_H1_tmul_eq_and_heckeTL_baseChange_and_map_parabolicHoms.solution
