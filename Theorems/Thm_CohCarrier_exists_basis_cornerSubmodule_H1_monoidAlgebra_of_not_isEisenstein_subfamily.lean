import Mathlib
import Definitions.Def_CohCarrier_SubfamilyHeckeData
import Definitions.Def_IharaLemma_IdempotentSplitting
import P2M.Util
import P2M.Sol.S_CohCarrier_exists_basis_cornerSubmodule_H1_monoidAlgebra_of_not_isEisenstein_subfamily

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
open scoped IsMulCommutative

theorem CohCarrier.exists_basis_cornerSubmodule_H1_monoidAlgebra_of_not_isEisenstein_subfamily
    (L : ℕ) [NeZero L] (S : Set ℕ)
    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪] [CharZero 𝒪]
    (p : ℕ) [Fact p.Prime] [CharP (IsLocalRing.ResidueField 𝒪) p]
    (H H' : Subgroup (ZMod L)ˣ) (hHH' : H ≤ H') (hidx : ∃ n : ℕ, H.relIndex H' = p ^ n)
    (r : ℕ) (hrL : r ∣ L) (hr : 4 ≤ r)
    (hH' : ∀ u ∈ H', ZMod.castHom hrL (ZMod r) (u : ZMod L) = 1)

    {G : Type} (φ : G → CohCarrier.Gen L S)
    (dG : ↥H' → G) (hdG : ∀ u : ↥H', φ (dG u) = CohCarrier.Gen.dia (u : (ZMod L)ˣ))
    (hcomm : ∀ g g' : G,
      CohCarrier.opFamily L H S 𝒪 (φ g) * CohCarrier.opFamily L H S 𝒪 (φ g') =
        CohCarrier.opFamily L H S 𝒪 (φ g') * CohCarrier.opFamily L H S 𝒪 (φ g))
    (hcomm' : ∀ g g' : G,
      CohCarrier.opFamily L H' S 𝒪 (φ g) * CohCarrier.opFamily L H' S 𝒪 (φ g') =
        CohCarrier.opFamily L H' S 𝒪 (φ g') * CohCarrier.opFamily L H' S 𝒪 (φ g))
    (θbar : G → IsLocalRing.ResidueField 𝒪)
    (Sp : IharaLemma.IdempotentSplitting
      ↥(CohCarrier.hdataSub L H S 𝒪 (IsLocalRing.ResidueField 𝒪) φ hcomm θbar).opSubalgebra)
    (i₀ : Fin Sp.n) (πk : Sp.CornerRing i₀ →ₐ[𝒪] IsLocalRing.ResidueField 𝒪)
    (hπk : ∀ g : G, πk (Sp.toCornerRing i₀
      ⟨(CohCarrier.hdataSub L H S 𝒪 (IsLocalRing.ResidueField 𝒪) φ hcomm θbar).op g,
        Algebra.subset_adjoin (Set.mem_range_self g)⟩) = θbar g)
    (Sp' : IharaLemma.IdempotentSplitting
      ↥(CohCarrier.hdataSub L H' S 𝒪 (IsLocalRing.ResidueField 𝒪) φ hcomm' θbar).opSubalgebra)
    (i₀' : Fin Sp'.n) (πk' : Sp'.CornerRing i₀' →ₐ[𝒪] IsLocalRing.ResidueField 𝒪)
    (hπk' : ∀ g : G, πk' (Sp'.toCornerRing i₀'
      ⟨(CohCarrier.hdataSub L H' S 𝒪 (IsLocalRing.ResidueField 𝒪) φ hcomm' θbar).op g,
        Algebra.subset_adjoin (Set.mem_range_self g)⟩) = θbar g)

    (hEis : ∃ (g : G) (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S) (hℓL : ¬ ℓ ∣ L),
      φ g = CohCarrier.Gen.T ℓ hℓ hℓS hℓL ∧ ℓ ≡ 1 [MOD L] ∧
        θbar g ≠ (ℓ : IsLocalRing.ResidueField 𝒪) + 1)

    {Δ : Type} [CommGroup Δ] (π : (ZMod L)ˣ →* Δ)
    (hπ : ∀ δ : Δ, ∃ u ∈ H', π u = δ) (hπH : ∀ u ∈ H', (π u = 1 ↔ u ∈ H))
    (ι : MonoidAlgebra 𝒪 Δ →ₐ[𝒪] Sp.CornerRing i₀)
    (hι : ∀ u : ↥H', ι (MonoidAlgebra.of 𝒪 Δ (π u)) = Sp.toCornerRing i₀
      ⟨(CohCarrier.hdataSub L H S 𝒪 (IsLocalRing.ResidueField 𝒪) φ hcomm θbar).op (dG u),
        Algebra.subset_adjoin (Set.mem_range_self (dG u))⟩) :
    ∃ b : Fin (Module.finrank 𝒪
        ↥(IharaLemma.cornerSubmodule (M := CohCarrier.H1 L H' 𝒪) (Sp'.e i₀'))) →
          ↥(IharaLemma.cornerSubmodule (M := CohCarrier.H1 L H 𝒪) (Sp.e i₀)),
      (∀ x : ↥(IharaLemma.cornerSubmodule (M := CohCarrier.H1 L H 𝒪) (Sp.e i₀)),
        ∃ c : Fin (Module.finrank 𝒪
            ↥(IharaLemma.cornerSubmodule (M := CohCarrier.H1 L H' 𝒪) (Sp'.e i₀'))) →
              MonoidAlgebra 𝒪 Δ,
          x = ∑ i, ι (c i) • b i) ∧
      (∀ c : Fin (Module.finrank 𝒪
            ↥(IharaLemma.cornerSubmodule (M := CohCarrier.H1 L H' 𝒪) (Sp'.e i₀'))) →
              MonoidAlgebra 𝒪 Δ,
        ∑ i, ι (c i) • b i = 0 ↔ ∀ i, c i = 0) := by p2m_exact_reverting @_root_.P2MW.S_CohCarrier_exists_basis_cornerSubmodule_H1_monoidAlgebra_of_not_isEisenstein_subfamily.solution
