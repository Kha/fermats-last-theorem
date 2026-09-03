import Definitions.Def_CohCarrier_Level
import P2M.Util
import P2M.Sol.S_CohCarrier_injective_iDeg_one_and_range_eq_of_isUnit_index
attribute [-instance] CohCarrier.HeckeData.V_isScalarTower CohCarrier.HeckeData.opSubalgebra_isMulCommutative CohCarrier.HeckeData.mTheta_isPrime
attribute [-simp] CohCarrier.Gen.dia.sizeOf_spec CohCarrier.Gen.U.injEq CohCarrier.Gen.T.sizeOf_spec CohCarrier.Gen.U.sizeOf_spec CohCarrier.Gen.T.injEq CohCarrier.Gen.dia.injEq CohCarrier.HeckeData.mk.sizeOf_spec CohCarrier.HeckeData.opAlgHom_X CohCarrier.HeckeData.toMLₒ_apply CohCarrier.HeckeData.mk.injEq

set_option autoImplicit false

open CongruenceSubgroup

theorem CohCarrier.injective_iDeg_one_and_range_eq_of_isUnit_index
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)
    (R : Type) [CommRing R] (A : Type) [AddCommGroup A] [Module R A]
    (h : CohCarrier.LevelLE M M ⊤ H 1)
    (hunit : IsUnit ((H.index : ℕ) : R)) :
    (CohCarrier.iotaDeg M M ⊤ H 1 h).range.index = H.index ∧
    Function.Injective (CohCarrier.iDeg' M M ⊤ H 1 A h) ∧
    Set.range (CohCarrier.iDeg' M M ⊤ H 1 A h) =
      {φ | ∀ σ : Gamma0 M, CohCarrier.diamondRaw M H A σ φ = φ} ∧
    ∀ φ : CohCarrier.H1 M H A, (∀ σ : Gamma0 M, CohCarrier.diamondRaw M H A σ φ = φ) →
      CohCarrier.iDeg' M M ⊤ H 1 A h (CohCarrier.jDeg M M ⊤ H 1 A h φ) = H.index • φ := by p2m_exact_reverting @_root_.P2MW.S_CohCarrier_injective_iDeg_one_and_range_eq_of_isUnit_index.solution
