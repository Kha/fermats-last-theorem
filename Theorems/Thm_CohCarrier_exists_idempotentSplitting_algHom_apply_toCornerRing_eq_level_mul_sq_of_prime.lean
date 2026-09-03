import Definitions.Def_CohCarrier_Inst
import Definitions.Def_IharaLemma_IdempotentSplitting
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import P2M.Util
import P2M.Sol.S_CohCarrier_exists_idempotentSplitting_algHom_apply_toCornerRing_eq_level_mul_sq_of_prime
attribute [-instance] CohCarrier.GammaHLower_finiteIndex
attribute [-simp] CohCarrier.uMat_apply_10 CohCarrier.rightQuotEquivOfDvd_apply CohCarrier.uMat_apply_11 CohCarrier.uMat_apply_01 CohCarrier.uMat_apply_00 CohCarrier.coe_uElt

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

open scoped IsMulCommutative

theorem CohCarrier.exists_idempotentSplitting_algHom_apply_toCornerRing_eq_level_mul_sq_of_prime
    (N q : ℕ) [NeZero N] [NeZero q] (hq : q.Prime) (hqN : ¬ q ∣ N)
    (h1 : CohCarrier.LevelLE N (N * q ^ 2) (⊤ : Subgroup (ZMod N)ˣ)
      (⊤ : Subgroup (ZMod (N * q ^ 2))ˣ) 1)
    (hq' : CohCarrier.LevelLE N (N * q ^ 2) (⊤ : Subgroup (ZMod N)ˣ)
      (⊤ : Subgroup (ZMod (N * q ^ 2))ˣ) q)
    (hq2 : CohCarrier.LevelLE N (N * q ^ 2) (⊤ : Subgroup (ZMod N)ˣ)
      (⊤ : Subgroup (ZMod (N * q ^ 2))ˣ) (q ^ 2))
    (S : Set ℕ) (hqS : q ∈ S)
    (𝒪 : Type) [CommRing 𝒪] [IsLocalRing 𝒪] [IsNoetherianRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
    (hcomm : ∀ g g' : CohCarrier.Gen N S,
      CohCarrier.opFamily N ⊤ S 𝒪 g * CohCarrier.opFamily N ⊤ S 𝒪 g' =
        CohCarrier.opFamily N ⊤ S 𝒪 g' * CohCarrier.opFamily N ⊤ S 𝒪 g)
    (hcomm' : ∀ g g' : CohCarrier.Gen (N * q ^ 2) S,
      CohCarrier.opFamily (N * q ^ 2) ⊤ S 𝒪 g * CohCarrier.opFamily (N * q ^ 2) ⊤ S 𝒪 g' =
        CohCarrier.opFamily (N * q ^ 2) ⊤ S 𝒪 g' * CohCarrier.opFamily (N * q ^ 2) ⊤ S 𝒪 g)
    (θbar : CohCarrier.Gen N S → IsLocalRing.ResidueField 𝒪)
    (θbar' : CohCarrier.Gen (N * q ^ 2) S → IsLocalRing.ResidueField 𝒪)

    (hθT : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S) (hℓM : ¬ ℓ ∣ N * q ^ 2),
      θbar' (CohCarrier.Gen.T ℓ hℓ hℓS hℓM) =
        θbar (CohCarrier.Gen.T ℓ hℓ hℓS (fun h => hℓM (Dvd.dvd.mul_right h (q ^ 2)))))
    (hθU : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ℓ ∣ N * q ^ 2) (hℓN : ℓ ∣ N),
      θbar' (CohCarrier.Gen.U ℓ hℓ hℓM) = θbar (CohCarrier.Gen.U ℓ hℓ hℓN))
    (hθq : θbar' (CohCarrier.Gen.U q hq (dvd_mul_of_dvd_right (dvd_pow_self q two_ne_zero) N)) = 0)
    (hθdia : ∀ d : (ZMod (N * q ^ 2))ˣ, θbar' (CohCarrier.Gen.dia d) = 1)

    (Sp : IharaLemma.IdempotentSplitting
      ↥(CohCarrier.hdata N ⊤ S 𝒪 (IsLocalRing.ResidueField 𝒪) hcomm θbar).opSubalgebra)
    (i₀ : Fin Sp.n) (πk : Sp.CornerRing i₀ →ₐ[𝒪] IsLocalRing.ResidueField 𝒪)
    (hπk : ∀ g : CohCarrier.Gen N S, πk (Sp.toCornerRing i₀
      ⟨(CohCarrier.hdata N ⊤ S 𝒪 (IsLocalRing.ResidueField 𝒪) hcomm θbar).op g,
        Algebra.subset_adjoin (Set.mem_range_self g)⟩) = θbar g)

    (hinj : ∀ φ : CohCarrier.H1 N ⊤ 𝒪,
      φ ∈ IharaLemma.cornerSubmodule (M := CohCarrier.H1 N ⊤ 𝒪) (Sp.e i₀) →
      ((q : 𝒪) • CohCarrier.iDegL N (N * q ^ 2) ⊤ ⊤ 1 𝒪 𝒪 h1
          - (CohCarrier.iDegL N (N * q ^ 2) ⊤ ⊤ q 𝒪 𝒪 hq').comp (CohCarrier.heckeTL N ⊤ 𝒪 q)
          + CohCarrier.iDegL N (N * q ^ 2) ⊤ ⊤ (q ^ 2) 𝒪 𝒪 hq2) φ = 0 → φ = 0) :
    ∃ (Sp' : IharaLemma.IdempotentSplitting
        ↥(CohCarrier.hdata (N * q ^ 2) ⊤ S 𝒪 (IsLocalRing.ResidueField 𝒪) hcomm' θbar').opSubalgebra)
      (i₀' : Fin Sp'.n) (πk' : Sp'.CornerRing i₀' →ₐ[𝒪] IsLocalRing.ResidueField 𝒪),
      ∀ g : CohCarrier.Gen (N * q ^ 2) S, πk' (Sp'.toCornerRing i₀'
        ⟨(CohCarrier.hdata (N * q ^ 2) ⊤ S 𝒪 (IsLocalRing.ResidueField 𝒪) hcomm' θbar').op g,
          Algebra.subset_adjoin (Set.mem_range_self g)⟩) = θbar' g := by p2m_exact_reverting @_root_.P2MW.S_CohCarrier_exists_idempotentSplitting_algHom_apply_toCornerRing_eq_level_mul_sq_of_prime.solution
