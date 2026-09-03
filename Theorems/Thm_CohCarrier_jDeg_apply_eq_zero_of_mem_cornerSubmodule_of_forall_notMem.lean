import Mathlib
import Definitions.Def_CohCarrier_Inst
import Definitions.Def_IharaLemma_IdempotentSplitting
import P2M.Util
import P2M.Sol.S_CohCarrier_jDeg_apply_eq_zero_of_mem_cornerSubmodule_of_forall_notMem

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
open scoped IsMulCommutative

theorem CohCarrier.jDeg_apply_eq_zero_of_mem_cornerSubmodule_of_forall_notMem
    (M q : ℕ) [NeZero M] [NeZero q]
    (h1 : CohCarrier.LevelLE M (M * q) (⊤ : Subgroup (ZMod M)ˣ) (⊤ : Subgroup (ZMod (M * q))ˣ) 1)
    (hq' : CohCarrier.LevelLE M (M * q) (⊤ : Subgroup (ZMod M)ˣ) (⊤ : Subgroup (ZMod (M * q))ˣ) q)
    (S : Set ℕ)
    (𝒪 : Type) [CommRing 𝒪] [IsLocalRing 𝒪] [IsNoetherianRing 𝒪]
    (hcomm : ∀ g g' : CohCarrier.Gen (M * q) S,
      CohCarrier.opFamily (M * q) ⊤ S 𝒪 g * CohCarrier.opFamily (M * q) ⊤ S 𝒪 g' =
        CohCarrier.opFamily (M * q) ⊤ S 𝒪 g' * CohCarrier.opFamily (M * q) ⊤ S 𝒪 g)
    (hcommM : ∀ g g' : CohCarrier.Gen M S,
      CohCarrier.opFamily M ⊤ S 𝒪 g * CohCarrier.opFamily M ⊤ S 𝒪 g' =
        CohCarrier.opFamily M ⊤ S 𝒪 g' * CohCarrier.opFamily M ⊤ S 𝒪 g)
    (θbar : CohCarrier.Gen (M * q) S → IsLocalRing.ResidueField 𝒪)
    (θbarM : CohCarrier.Gen M S → IsLocalRing.ResidueField 𝒪)

    (Sp : IharaLemma.IdempotentSplitting
      ↥(CohCarrier.hdata (M * q) ⊤ S 𝒪 (IsLocalRing.ResidueField 𝒪) hcomm θbar).opSubalgebra)
    (i₀ : Fin Sp.n) (πk : Sp.CornerRing i₀ →ₐ[𝒪] IsLocalRing.ResidueField 𝒪)
    (hπk : ∀ g : CohCarrier.Gen (M * q) S, πk (Sp.toCornerRing i₀
      ⟨(CohCarrier.hdata (M * q) ⊤ S 𝒪 (IsLocalRing.ResidueField 𝒪) hcomm θbar).op g,
        Algebra.subset_adjoin (Set.mem_range_self g)⟩) = θbar g)

    (SpM : IharaLemma.IdempotentSplitting
      ↥(CohCarrier.hdata M ⊤ S 𝒪 (IsLocalRing.ResidueField 𝒪) hcommM θbarM).opSubalgebra)
    (hne : ∀ i' : Fin SpM.n,
      ∃ f : MvPolynomial {ℓ : ℕ // ℓ.Prime ∧ ℓ ∉ S ∧ ¬ ℓ ∣ M * q} 𝒪,
        MvPolynomial.aeval (R := 𝒪)
            (fun ℓ => θbar (CohCarrier.Gen.T ℓ.1 ℓ.2.1 ℓ.2.2.1 ℓ.2.2.2)) f = 0 ∧
        MvPolynomial.aeval (R := 𝒪)
            (fun ℓ => (⟨(CohCarrier.hdata M ⊤ S 𝒪 (IsLocalRing.ResidueField 𝒪) hcommM θbarM).op
                (CohCarrier.Gen.T ℓ.1 ℓ.2.1 ℓ.2.2.1 (fun h => ℓ.2.2.2 (Dvd.dvd.mul_right h q))),
              Algebra.subset_adjoin (Set.mem_range_self _)⟩ :
              ↥(CohCarrier.hdata M ⊤ S 𝒪 (IsLocalRing.ResidueField 𝒪) hcommM θbarM).opSubalgebra)) f
          ∉ SpM.𝔪 i')
    (v : CohCarrier.H1 (M * q) ⊤ 𝒪)
    (hv : v ∈ IharaLemma.cornerSubmodule (M := CohCarrier.H1 (M * q) ⊤ 𝒪) (Sp.e i₀)) :
    CohCarrier.jDeg M (M * q) ⊤ ⊤ 1 𝒪 h1 v = 0 ∧ CohCarrier.jDeg M (M * q) ⊤ ⊤ q 𝒪 hq' v = 0 := by p2m_exact_reverting @_root_.P2MW.S_CohCarrier_jDeg_apply_eq_zero_of_mem_cornerSubmodule_of_forall_notMem.solution
