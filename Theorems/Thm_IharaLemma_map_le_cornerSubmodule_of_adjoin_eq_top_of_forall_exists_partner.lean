import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.Finiteness.Defs
import Definitions.Def_IharaLemma_IdempotentSplitting
import P2M.Util
import P2M.Sol.S_IharaLemma_map_le_cornerSubmodule_of_adjoin_eq_top_of_forall_exists_partner

set_option autoImplicit false

theorem IharaLemma.map_le_cornerSubmodule_of_adjoin_eq_top_of_forall_exists_partner
    {𝒪 : Type} [CommRing 𝒪] [IsLocalRing 𝒪]
    {B B' : Type} [CommRing B] [CommRing B'] [Algebra 𝒪 B] [Algebra 𝒪 B']
    [Module.Finite 𝒪 B] [Module.Finite 𝒪 B']
    {V V' : Type} [AddCommGroup V] [Module 𝒪 V] [Module B V] [IsScalarTower 𝒪 B V]
    [AddCommGroup V'] [Module 𝒪 V'] [Module B' V'] [IsScalarTower 𝒪 B' V']
    (f : V →ₗ[𝒪] V') (S : IharaLemma.IdempotentSplitting B) (i : Fin S.n)
    (S' : IharaLemma.IdempotentSplitting B') (i' : Fin S'.n)
    (hsep : ∀ v' : V', (∀ k : ℕ, v' ∈ ((IsLocalRing.maximalIdeal 𝒪) ^ k • ⊤ : Submodule 𝒪 V')) → v' = 0)
    (G' : Set B') (hG' : Algebra.adjoin 𝒪 G' = ⊤)
    (hgen : ∀ g' ∈ G', ∃ (c : 𝒪) (g₀ : B), g' - algebraMap 𝒪 B' c ∈ S'.𝔪 i' ∧
      g₀ - algebraMap 𝒪 B c ∈ S.𝔪 i ∧ ∀ v : V, f (g₀ • v) = g' • f v) :
    ∀ w ∈ IharaLemma.cornerSubmodule (M := V) (S.e i),
      f w ∈ IharaLemma.cornerSubmodule (M := V') (S'.e i') := by p2m_exact_reverting @_root_.P2MW.S_IharaLemma_map_le_cornerSubmodule_of_adjoin_eq_top_of_forall_exists_partner.solution
