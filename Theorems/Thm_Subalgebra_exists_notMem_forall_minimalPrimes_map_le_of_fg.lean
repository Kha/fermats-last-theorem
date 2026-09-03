import Mathlib
import P2M.Util
import P2M.Sol.S_Subalgebra_exists_notMem_forall_minimalPrimes_map_le_of_fg

set_option autoImplicit false

theorem Subalgebra.exists_notMem_forall_minimalPrimes_map_le_of_fg
    {R F : Type*} [CommRing R] [IsNoetherianRing R] [Field F] [Algebra R F]
    (B : Subalgebra R F) (hfg : B.FG) (I : Ideal R)
    (𝔪 : Ideal ↥B) [𝔪.IsPrime] (hI : I.map (algebraMap R ↥B) ≤ 𝔪) :
    ∃ (h : F) (hhB : h ∈ B), (⟨h, hhB⟩ : ↥B) ∉ 𝔪 ∧
      ∀ 𝔮 : Ideal ↥(Algebra.adjoin R ((B : Set F) ∪ {h⁻¹})),
        𝔮 ∈ (I.map (algebraMap R ↥(Algebra.adjoin R ((B : Set F) ∪ {h⁻¹})))).minimalPrimes →
        ∀ (b : F) (hb : b ∈ B), (⟨b, Algebra.subset_adjoin (Set.mem_union_left _ hb)⟩ :
            ↥(Algebra.adjoin R ((B : Set F) ∪ {h⁻¹}))) ∈ 𝔮 → (⟨b, hb⟩ : ↥B) ∈ 𝔪 := by p2m_exact_reverting @_root_.P2MW.S_Subalgebra_exists_notMem_forall_minimalPrimes_map_le_of_fg.solution
