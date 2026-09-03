import Definitions.Def_CohCarrier_Level
import P2M.Util
import P2M.Sol.S_CohCarrier_exists_gamma0_lift_dvd
attribute [-instance] CohCarrier.HeckeData.V_isScalarTower CohCarrier.HeckeData.opSubalgebra_isMulCommutative CohCarrier.HeckeData.mTheta_isPrime
attribute [-simp] CohCarrier.Gen.dia.sizeOf_spec CohCarrier.Gen.U.injEq CohCarrier.Gen.T.sizeOf_spec CohCarrier.Gen.U.sizeOf_spec CohCarrier.Gen.T.injEq CohCarrier.Gen.dia.injEq CohCarrier.HeckeData.mk.sizeOf_spec CohCarrier.HeckeData.opAlgHom_X CohCarrier.HeckeData.toMLₒ_apply CohCarrier.HeckeData.mk.injEq

set_option autoImplicit false
open CongruenceSubgroup
open scoped MatrixGroups

theorem CohCarrier.exists_gamma0_lift_dvd (M ℓ : ℕ) [NeZero M] [NeZero ℓ] (d : (ZMod M)ˣ) :
    ∃ σ : Gamma0 M, gamma0Units M σ = d ∧ ((ℓ * M : ℕ) : ℤ) ∣ ((σ : SL(2, ℤ)) 1 0) := by p2m_exact_reverting @_root_.P2MW.S_CohCarrier_exists_gamma0_lift_dvd.solution
