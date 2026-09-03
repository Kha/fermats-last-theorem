import Mathlib
import Definitions.Def_CohCarrier_Level
import Definitions.Def_ModularCurve_PeriodMap
import P2M.Util
import P2M.Sol.S_CohCarrier_heckeT_mem_parabolicHoms
attribute [-instance] CohCarrier.HeckeData.V_isScalarTower CohCarrier.HeckeData.opSubalgebra_isMulCommutative CohCarrier.HeckeData.mTheta_isPrime
attribute [-simp] CohCarrier.Gen.dia.sizeOf_spec CohCarrier.Gen.U.injEq CohCarrier.Gen.T.sizeOf_spec CohCarrier.Gen.U.sizeOf_spec CohCarrier.Gen.T.injEq CohCarrier.Gen.dia.injEq CohCarrier.HeckeData.mk.sizeOf_spec CohCarrier.HeckeData.opAlgHom_X CohCarrier.HeckeData.toMLₒ_apply CohCarrier.HeckeData.mk.injEq

set_option autoImplicit false

theorem CohCarrier.heckeT_mem_parabolicHoms (M : ℕ) (H : Subgroup (ZMod M)ˣ) (A : Type*) [AddCommGroup A]
    (ℓ : ℕ) [NeZero ℓ] (φ : CohCarrier.H1 M H A)
    (hφ : φ ∈ ModularCurve.Period.parabolicHoms ℤ (CohCarrier.GammaH M H) A) :
    CohCarrier.heckeT M H ℓ A φ ∈ ModularCurve.Period.parabolicHoms ℤ (CohCarrier.GammaH M H) A := by p2m_exact_reverting @_root_.P2MW.S_CohCarrier_heckeT_mem_parabolicHoms.solution
