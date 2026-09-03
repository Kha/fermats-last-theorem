import Definitions.Def_CohCarrier_Inst
import Definitions.Def_IharaLemma_IdempotentSplitting
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import P2M.Util
import P2M.Sol.S_CohCarrier_exists_idempotentSplitting_algHom_apply_toCornerRing_eq_level_mul_of_prime_of_dvd
attribute [-instance] CohCarrier.GammaHLower_finiteIndex
attribute [-simp] CohCarrier.uMat_apply_10 CohCarrier.rightQuotEquivOfDvd_apply CohCarrier.uMat_apply_11 CohCarrier.uMat_apply_01 CohCarrier.uMat_apply_00 CohCarrier.coe_uElt

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

open scoped IsMulCommutative

theorem CohCarrier.exists_idempotentSplitting_algHom_apply_toCornerRing_eq_level_mul_of_prime_of_dvd
    (N q : ℕ) [NeZero N] [NeZero q] (hq : q.Prime) (hqN : q ∣ N)
    (h1 : CohCarrier.LevelLE N (N * q) (⊤ : Subgroup (ZMod N)ˣ)
      (⊤ : Subgroup (ZMod (N * q))ˣ) 1)
    (hq' : CohCarrier.LevelLE N (N * q) (⊤ : Subgroup (ZMod N)ˣ)
      (⊤ : Subgroup (ZMod (N * q))ˣ) q)
    (S : Set ℕ)
    (𝒪 : Type) [CommRing 𝒪] [IsLocalRing 𝒪] [IsNoetherianRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
    (hcomm : ∀ g g' : CohCarrier.Gen N S,
      CohCarrier.opFamily N ⊤ S 𝒪 g * CohCarrier.opFamily N ⊤ S 𝒪 g' =
        CohCarrier.opFamily N ⊤ S 𝒪 g' * CohCarrier.opFamily N ⊤ S 𝒪 g)
    (hcomm' : ∀ g g' : CohCarrier.Gen (N * q) S,
      CohCarrier.opFamily (N * q) ⊤ S 𝒪 g * CohCarrier.opFamily (N * q) ⊤ S 𝒪 g' =
        CohCarrier.opFamily (N * q) ⊤ S 𝒪 g' * CohCarrier.opFamily (N * q) ⊤ S 𝒪 g)
    (θbar : CohCarrier.Gen N S → IsLocalRing.ResidueField 𝒪)
    (θbar' : CohCarrier.Gen (N * q) S → IsLocalRing.ResidueField 𝒪)

    (hθT : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S) (hℓM : ¬ ℓ ∣ N * q),
      θbar' (CohCarrier.Gen.T ℓ hℓ hℓS hℓM) =
        θbar (CohCarrier.Gen.T ℓ hℓ hℓS (fun h => hℓM (Dvd.dvd.mul_right h q))))
    (hθU : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ℓ ∣ N * q) (hℓN : ℓ ∣ N), ℓ ≠ q →
      θbar' (CohCarrier.Gen.U ℓ hℓ hℓM) = θbar (CohCarrier.Gen.U ℓ hℓ hℓN))
    (hθq : θbar' (CohCarrier.Gen.U q hq (dvd_mul_left q N)) = 0)
    (hθdia : ∀ d : (ZMod (N * q))ˣ, θbar' (CohCarrier.Gen.dia d) = 1)

    (Sp : IharaLemma.IdempotentSplitting
      ↥(CohCarrier.hdata N ⊤ S 𝒪 (IsLocalRing.ResidueField 𝒪) hcomm θbar).opSubalgebra)
    (i₀ : Fin Sp.n) (πk : Sp.CornerRing i₀ →ₐ[𝒪] IsLocalRing.ResidueField 𝒪)
    (hπk : ∀ g : CohCarrier.Gen N S, πk (Sp.toCornerRing i₀
      ⟨(CohCarrier.hdata N ⊤ S 𝒪 (IsLocalRing.ResidueField 𝒪) hcomm θbar).op g,
        Algebra.subset_adjoin (Set.mem_range_self g)⟩) = θbar g)

    (hinj : ∀ φ : CohCarrier.H1 N ⊤ 𝒪,
      φ ∈ IharaLemma.cornerSubmodule (M := CohCarrier.H1 N ⊤ 𝒪) (Sp.e i₀) →
      ((CohCarrier.iDegL N (N * q) ⊤ ⊤ q 𝒪 𝒪 hq').comp (CohCarrier.heckeTL N ⊤ 𝒪 q)
          - (q : 𝒪) • CohCarrier.iDegL N (N * q) ⊤ ⊤ 1 𝒪 𝒪 h1) φ = 0 → φ = 0) :
    ∃ (Sp' : IharaLemma.IdempotentSplitting
        ↥(CohCarrier.hdata (N * q) ⊤ S 𝒪 (IsLocalRing.ResidueField 𝒪) hcomm' θbar').opSubalgebra)
      (i₀' : Fin Sp'.n) (πk' : Sp'.CornerRing i₀' →ₐ[𝒪] IsLocalRing.ResidueField 𝒪),
      ∀ g : CohCarrier.Gen (N * q) S, πk' (Sp'.toCornerRing i₀'
        ⟨(CohCarrier.hdata (N * q) ⊤ S 𝒪 (IsLocalRing.ResidueField 𝒪) hcomm' θbar').op g,
          Algebra.subset_adjoin (Set.mem_range_self g)⟩) = θbar' g := by p2m_exact_reverting @_root_.P2MW.S_CohCarrier_exists_idempotentSplitting_algHom_apply_toCornerRing_eq_level_mul_of_prime_of_dvd.solution
