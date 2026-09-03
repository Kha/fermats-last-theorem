import Definitions.Def_CohCarrier_Level
import Definitions.Def_ModularCurve_PeriodMap
import P2M.Util
import P2M.Sol.S_CohCarrier_mem_map_iDegL_one_parabolicHoms_iff
attribute [-instance] CohCarrier.HeckeData.V_isScalarTower CohCarrier.HeckeData.opSubalgebra_isMulCommutative CohCarrier.HeckeData.mTheta_isPrime
attribute [-simp] CohCarrier.Gen.dia.sizeOf_spec CohCarrier.Gen.U.injEq CohCarrier.Gen.T.sizeOf_spec CohCarrier.Gen.U.sizeOf_spec CohCarrier.Gen.T.injEq CohCarrier.Gen.dia.injEq CohCarrier.HeckeData.mk.sizeOf_spec CohCarrier.HeckeData.opAlgHom_X CohCarrier.HeckeData.toMLₒ_apply CohCarrier.HeckeData.mk.injEq

set_option autoImplicit false

open scoped MatrixGroups

theorem CohCarrier.mem_map_iDegL_one_parabolicHoms_iff
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)
    (R : Type) [CommRing R] (A : Type) [AddCommGroup A] [Module R A]
    (h₁ : CohCarrier.LevelLE M M ⊤ H 1) (hunit : IsUnit ((H.index : ℕ) : R)) (φ : CohCarrier.H1 M H A) :
    φ ∈ (ModularCurve.Period.parabolicHoms R (CohCarrier.GammaH M ⊤) A).map
        (CohCarrier.iDegL M M ⊤ H 1 A R h₁) ↔
      (φ ∈ ModularCurve.Period.parabolicHoms R (CohCarrier.GammaH M H) A ∧
        ∀ σ : CongruenceSubgroup.Gamma0 M, CohCarrier.diamondRaw M H A σ φ = φ) := by p2m_exact_reverting @_root_.P2MW.S_CohCarrier_mem_map_iDegL_one_parabolicHoms_iff.solution
