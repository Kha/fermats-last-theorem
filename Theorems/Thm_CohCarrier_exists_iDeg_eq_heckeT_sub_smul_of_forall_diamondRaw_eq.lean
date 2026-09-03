import Mathlib
import Definitions.Def_CohCarrier_Level
import P2M.Util
import P2M.Sol.S_CohCarrier_exists_iDeg_eq_heckeT_sub_smul_of_forall_diamondRaw_eq
attribute [-instance] CohCarrier.HeckeData.V_isScalarTower CohCarrier.HeckeData.opSubalgebra_isMulCommutative CohCarrier.HeckeData.mTheta_isPrime
attribute [-simp] CohCarrier.Gen.dia.sizeOf_spec CohCarrier.Gen.U.injEq CohCarrier.Gen.T.sizeOf_spec CohCarrier.Gen.U.sizeOf_spec CohCarrier.Gen.T.injEq CohCarrier.Gen.dia.injEq CohCarrier.HeckeData.mk.sizeOf_spec CohCarrier.HeckeData.opAlgHom_X CohCarrier.HeckeData.toMLₒ_apply CohCarrier.HeckeData.mk.injEq

set_option autoImplicit false

open scoped MatrixGroups

theorem CohCarrier.exists_iDeg_eq_heckeT_sub_smul_of_forall_diamondRaw_eq
    (L : ℕ) [NeZero L] (A : Type) [AddCommGroup A]
    (H H' : Subgroup (ZMod L)ˣ) (h : CohCarrier.LevelLE L L H' H 1)
    (hA : ∀ a : A, H.relIndex H' • a = 0 → a = 0)
    (ℓ : ℕ) [NeZero ℓ] (hℓ : ℓ.Prime) (hℓL : ¬ ℓ ∣ L)
    (φ : CohCarrier.H1 L H A)
    (hφ : ∀ σ : ↥(CongruenceSubgroup.Gamma0 L), (σ : SL(2, ℤ)) ∈ CohCarrier.GammaH L H' →
      CohCarrier.diamondRaw L H A σ φ = φ) :
    ∃ ψ : CohCarrier.H1 L H' A,
      CohCarrier.iDeg' L L H' H 1 A h ψ = CohCarrier.heckeT L H ℓ A φ - (ℓ + 1) • φ := by p2m_exact_reverting @_root_.P2MW.S_CohCarrier_exists_iDeg_eq_heckeT_sub_smul_of_forall_diamondRaw_eq.solution
