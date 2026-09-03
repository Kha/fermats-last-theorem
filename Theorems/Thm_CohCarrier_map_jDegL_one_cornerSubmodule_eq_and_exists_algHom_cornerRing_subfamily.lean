import Mathlib
import Definitions.Def_CohCarrier_SubfamilyHeckeData
import Definitions.Def_IharaLemma_IdempotentSplitting
import P2M.Util
import P2M.Sol.S_CohCarrier_map_jDegL_one_cornerSubmodule_eq_and_exists_algHom_cornerRing_subfamily

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
open scoped IsMulCommutative

theorem CohCarrier.map_jDegL_one_cornerSubmodule_eq_and_exists_algHom_cornerRing_subfamily
    (L : ℕ) [NeZero L] (S : Set ℕ)
    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪] [CharZero 𝒪]
    (H H' : Subgroup (ZMod L)ˣ) (h : CohCarrier.LevelLE L L H' H 1)
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
        Algebra.subset_adjoin (Set.mem_range_self g)⟩) = θbar g) :

    Submodule.map (CohCarrier.jDegL L L H' H 1 𝒪 𝒪 h)
        ((IharaLemma.cornerSubmodule (M := CohCarrier.H1 L H 𝒪) (Sp.e i₀)).restrictScalars 𝒪) =
      (IharaLemma.cornerSubmodule (M := CohCarrier.H1 L H' 𝒪) (Sp'.e i₀')).restrictScalars 𝒪 ∧

    (∀ m : CohCarrier.H1 L H 𝒪,
      m ∈ IharaLemma.cornerSubmodule (M := CohCarrier.H1 L H 𝒪) (Sp.e i₀) →
        (CohCarrier.jDegL L L H' H 1 𝒪 𝒪 h m = 0 ↔
          m ∈ Submodule.span 𝒪 {y : CohCarrier.H1 L H 𝒪 | ∃ u ∈ H',
            ∃ x ∈ IharaLemma.cornerSubmodule (M := CohCarrier.H1 L H 𝒪) (Sp.e i₀),
              y = CohCarrier.diamondL L H 𝒪 u x - x})) ∧

    ∃ Φ : Sp.CornerRing i₀ →ₐ[𝒪] Sp'.CornerRing i₀',
      Function.Surjective Φ ∧
      (∀ g : G,
        Φ (Sp.toCornerRing i₀
            ⟨(CohCarrier.hdataSub L H S 𝒪 (IsLocalRing.ResidueField 𝒪) φ hcomm θbar).op g,
              Algebra.subset_adjoin (Set.mem_range_self g)⟩) =
          Sp'.toCornerRing i₀'
            ⟨(CohCarrier.hdataSub L H' S 𝒪 (IsLocalRing.ResidueField 𝒪) φ hcomm' θbar).op g,
              Algebra.subset_adjoin (Set.mem_range_self g)⟩) ∧
      (∀ (z : Sp.CornerRing i₀) (m : CohCarrier.H1 L H 𝒪),
        m ∈ IharaLemma.cornerSubmodule (M := CohCarrier.H1 L H 𝒪) (Sp.e i₀) →
          CohCarrier.jDegL L L H' H 1 𝒪 𝒪 h
              ((z : ↥(CohCarrier.hdataSub L H S 𝒪 (IsLocalRing.ResidueField 𝒪) φ hcomm θbar).opSubalgebra)
                • m) =
            ((Φ z : Sp'.CornerRing i₀') :
                ↥(CohCarrier.hdataSub L H' S 𝒪 (IsLocalRing.ResidueField 𝒪) φ hcomm' θbar).opSubalgebra)
              • CohCarrier.jDegL L L H' H 1 𝒪 𝒪 h m) := by p2m_exact_reverting @_root_.P2MW.S_CohCarrier_map_jDegL_one_cornerSubmodule_eq_and_exists_algHom_cornerRing_subfamily.solution
