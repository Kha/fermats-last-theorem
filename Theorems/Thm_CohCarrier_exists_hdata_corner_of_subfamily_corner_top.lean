import Definitions.Def_CuspForm_HeckeLocal
import Definitions.Def_CohCarrier_Inst
import Definitions.Def_IharaLemma_IdempotentSplitting
import Mathlib.LinearAlgebra.Dimension.Finrank
import P2M.Util
import P2M.Sol.S_CohCarrier_exists_hdata_corner_of_subfamily_corner_top

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 400000

open IsLocalRing CohCarrier IharaLemma

open scoped IsMulCommutative in

theorem CohCarrier.exists_hdata_corner_of_subfamily_corner_top
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (maximalIdeal 𝒪) 𝒪] [Finite (ResidueField 𝒪)] [CharZero 𝒪]
    (M : ℕ) [NeZero M]

    (S : Finset ℕ) (S₀ : Set ℕ) (hS₀fin : S₀.Finite)
    (hS₀M : ∀ q : ℕ, q.Prime → q ∣ M → q ∉ S₀)
    (hSS₀ : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ M → (ℓ ∈ S₀ ↔ ℓ ∈ (↑S : Set ℕ)))

    (hcomm : ∀ g h : CohCarrier.Gen M S₀,
      CohCarrier.opFamily M ⊤ S₀ 𝒪 g * CohCarrier.opFamily M ⊤ S₀ 𝒪 h =
        CohCarrier.opFamily M ⊤ S₀ 𝒪 h * CohCarrier.opFamily M ⊤ S₀ 𝒪 g)

    {𝕋 : Type} [CommRing 𝕋] [Algebra 𝒪 𝕋] [Module 𝕋 (H1 M ⊤ 𝒪)] [IsScalarTower 𝒪 𝕋 (H1 M ⊤ 𝒪)]
    [Module.Finite 𝒪 𝕋]
    (Sp : IdempotentSplitting 𝕋) (i : Fin Sp.n)
    [Module.Finite 𝒪 ↥(cornerSubmodule (M := H1 M ⊤ 𝒪) (Sp.e i))]
    [Module.Free 𝒪 ↥(cornerSubmodule (M := H1 M ⊤ 𝒪) (Sp.e i))]
    (tfull : CohCarrier.Gen M (↑S : Set ℕ) → 𝕋) (cfull : CohCarrier.Gen M (↑S : Set ℕ) → 𝒪)
    (hgen : ∀ x : 𝕋, ∃ f ∈ Algebra.adjoin 𝒪 (Set.range (CohCarrier.opFamily M ⊤ (↑S : Set ℕ) 𝒪)),
      ∀ m : H1 M ⊤ 𝒪, x • m = f m)
    (htfull : ∀ g, ∀ m : H1 M ⊤ 𝒪, tfull g • m = CohCarrier.opFamily M ⊤ (↑S : Set ℕ) 𝒪 g m)
    (hcfull : ∀ g, tfull g - algebraMap 𝒪 𝕋 (cfull g) ∈ Sp.𝔪 i)
    (hcofull : ∀ v : H1 M ⊤ 𝒪, (∀ g, ∀ k : ℕ, ∃ n : ℕ, ((tfull g - algebraMap 𝒪 𝕋 (cfull g)) ^ n) • v ∈
        ((maximalIdeal 𝒪) ^ k • ⊤ : Submodule 𝒪 (H1 M ⊤ 𝒪))) →
      v ∈ cornerSubmodule (M := H1 M ⊤ 𝒪) (Sp.e i))
    (hcd : ∀ d : (ZMod M)ˣ, cfull (.dia d) - 1 ∈ maximalIdeal 𝒪)
    (hocc : cornerSubmodule (M := H1 M ⊤ 𝒪) (Sp.e i) ≠ ⊥)
    (hfaith : ∀ x : Sp.CornerRing i,
      (∀ m : ↥(cornerSubmodule (M := H1 M ⊤ 𝒪) (Sp.e i)), x • m = 0) → x = 0) :
    ∃ (θbar : CohCarrier.Gen M S₀ → ResidueField 𝒪)

      (_ : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS₀ : ℓ ∉ S₀) (hℓM : ¬ ℓ ∣ M),
        θbar (.T ℓ hℓ hℓS₀ hℓM) =
          residue 𝒪 (cfull (.T ℓ hℓ (fun h => hℓS₀ ((hSS₀ ℓ hℓ hℓM).2 h)) hℓM)))
      (_ : ∀ (q : ℕ) (hq : q.Prime) (hqM : q ∣ M), θbar (.U q hq hqM) = residue 𝒪 (cfull (.U q hq hqM)))
      (_ : ∀ d : (ZMod M)ˣ, θbar (.dia d) = 1)
      (Sp' : IdempotentSplitting ↥(CohCarrier.hdata M ⊤ S₀ 𝒪 (ResidueField 𝒪) hcomm θbar).opSubalgebra)
      (i₀ : Fin Sp'.n) (πk : Sp'.CornerRing i₀ →ₐ[𝒪] ResidueField 𝒪)
      (_ : ∀ g : CohCarrier.Gen M S₀, πk (Sp'.toCornerRing i₀
        ⟨(CohCarrier.hdata M ⊤ S₀ 𝒪 (ResidueField 𝒪) hcomm θbar).op g,
          Algebra.subset_adjoin (Set.mem_range_self g)⟩) = θbar g)
      (eB : Sp.CornerRing i ≃ₐ[𝒪] Sp'.CornerRing i₀),

      (∀ v : H1 M ⊤ 𝒪, v ∈ cornerSubmodule (M := H1 M ⊤ 𝒪) (Sp.e i) ↔
        v ∈ cornerSubmodule (M := H1 M ⊤ 𝒪) (Sp'.e i₀)) ∧

      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ (↑S : Set ℕ)) (hℓM : ¬ ℓ ∣ M),
        eB (Sp.toCornerRing i (tfull (.T ℓ hℓ hℓS hℓM))) =
          Sp'.toCornerRing i₀
            ⟨(CohCarrier.hdata M ⊤ S₀ 𝒪 (ResidueField 𝒪) hcomm θbar).op
                (.T ℓ hℓ (fun h => hℓS ((hSS₀ ℓ hℓ hℓM).1 h)) hℓM),
              Algebra.subset_adjoin (Set.mem_range_self _)⟩) ∧
      (∀ (q : ℕ) (hq : q.Prime) (hqM : q ∣ M),
        eB (Sp.toCornerRing i (tfull (.U q hq hqM))) =
          Sp'.toCornerRing i₀
            ⟨(CohCarrier.hdata M ⊤ S₀ 𝒪 (ResidueField 𝒪) hcomm θbar).op (.U q hq hqM),
              Algebra.subset_adjoin (Set.mem_range_self _)⟩) ∧

      (∀ (x : Sp.CornerRing i) (m : ↥(cornerSubmodule (M := H1 M ⊤ 𝒪) (Sp.e i)))
          (m' : ↥(cornerSubmodule (M := H1 M ⊤ 𝒪) (Sp'.e i₀))),
        (m : H1 M ⊤ 𝒪) = m' → ((x • m : ↥(cornerSubmodule (M := H1 M ⊤ 𝒪) (Sp.e i))) : H1 M ⊤ 𝒪) =
          ((eB x • m' : ↥(cornerSubmodule (M := H1 M ⊤ 𝒪) (Sp'.e i₀))) : H1 M ⊤ 𝒪)) := by p2m_exact_reverting @_root_.P2MW.S_CohCarrier_exists_hdata_corner_of_subfamily_corner_top.solution
