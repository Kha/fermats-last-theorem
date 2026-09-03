import Mathlib
import Definitions.Def_CohCarrier_Tower
import P2M.Util
import P2M.Sol.S_CohCarrier_isEis_of_iDeg_add_eq_zero_of_diamond_invariant
attribute [-instance] CohCarrier.GammaHLower_finiteIndex CohCarrier.HeckeData.V_isScalarTower CohCarrier.HeckeData.opSubalgebra_isMulCommutative CohCarrier.HeckeData.mTheta_isPrime
attribute [-simp] CohCarrier.uMat_apply_10 CohCarrier.rightQuotEquivOfDvd_apply CohCarrier.uMat_apply_11 CohCarrier.uMat_apply_01 CohCarrier.uMat_apply_00 CohCarrier.coe_uElt CohCarrier.Gen.dia.sizeOf_spec CohCarrier.Gen.U.injEq CohCarrier.Gen.T.sizeOf_spec CohCarrier.Gen.U.sizeOf_spec CohCarrier.Gen.T.injEq CohCarrier.Gen.dia.injEq CohCarrier.HeckeData.mk.sizeOf_spec CohCarrier.HeckeData.opAlgHom_X CohCarrier.HeckeData.toMLₒ_apply CohCarrier.HeckeData.mk.injEq

set_option autoImplicit false

p2m_open "CohCarrier~iDeg_heckeT_comm_of_coprime~injective_iDeg_one_and_range_eq_of_isUnit_index~iDeg_comp CongruenceSubgroup"
open scoped MatrixGroups

theorem CohCarrier.isEis_of_iDeg_add_eq_zero_of_diamond_invariant
    (R : Type) [CommRing R] (A : Type) [AddCommGroup A] [Module R A] (ℓ₀ : ℕ) [NeZero ℓ₀]
    (N q : ℕ) [NeZero N] [NeZero q] (H : Subgroup (ZMod N)ˣ) (H' : Subgroup (ZMod (N * q))ˣ)
    (h₁ : LevelLE N (N * q) H H' 1) (hq : LevelLE N (N * q) H H' q)
    (h₁top : LevelLE N (N * q) (⊤ : Subgroup (ZMod N)ˣ) (⊤ : Subgroup (ZMod (N * q))ˣ) 1)
    (hqtop : LevelLE N (N * q) (⊤ : Subgroup (ZMod N)ˣ) (⊤ : Subgroup (ZMod (N * q))ˣ) q)
    (hℓ : ℓ₀.Prime) (hℓNq : ¬ ℓ₀ ∣ N * q)
    (hunit : IsUnit ((H.index : ℕ) : R)) (hunit' : IsUnit ((H'.index : ℕ) : R))
    (hihara_top : ∀ g₀ h₀ : H1 N ⊤ A,
      iDeg' N (N * q) ⊤ ⊤ 1 A h₁top g₀ + iDeg' N (N * q) ⊤ ⊤ q A hqtop h₀ = 0 →
        IsEis R A N ⊤ ℓ₀ g₀ ∧ IsEis R A N ⊤ ℓ₀ h₀)
    (g h : H1 N H A)
    (hg : ∀ σ : Gamma0 N, diamondRaw N H A σ g = g) (hh : ∀ σ : Gamma0 N, diamondRaw N H A σ h = h)
    (hgh : iDeg' N (N * q) H H' 1 A h₁ g + iDeg' N (N * q) H H' q A hq h = 0) :
    IsEis R A N H ℓ₀ g ∧ IsEis R A N H ℓ₀ h := by p2m_exact_reverting @_root_.P2MW.S_CohCarrier_isEis_of_iDeg_add_eq_zero_of_diamond_invariant.solution
