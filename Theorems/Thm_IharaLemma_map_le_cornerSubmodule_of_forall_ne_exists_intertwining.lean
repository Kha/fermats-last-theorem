import Mathlib.RingTheory.Ideal.Operations
import Definitions.Def_IharaLemma_IdempotentSplitting
import P2M.Util
import P2M.Sol.S_IharaLemma_map_le_cornerSubmodule_of_forall_ne_exists_intertwining

set_option autoImplicit false

open IharaLemma

theorem IharaLemma.map_le_cornerSubmodule_of_forall_ne_exists_intertwining
    {𝒪 : Type} [CommRing 𝒪] {B' : Type} [CommRing B'] [Algebra 𝒪 B']
    {V : Type} [AddCommGroup V] [Module 𝒪 V]
    {V' : Type} [AddCommGroup V'] [Module 𝒪 V'] [Module B' V'] [IsScalarTower 𝒪 B' V']
    (f : V →ₗ[𝒪] V') (S' : IdempotentSplitting B') (i' : Fin S'.n)
    (W : Submodule 𝒪 V) (I : Ideal 𝒪)
    (hsep : ∀ v' : V', (∀ k : ℕ, v' ∈ (I ^ k • ⊤ : Submodule 𝒪 V')) → v' = 0)
    (hyp : ∀ j' : Fin S'.n, j' ≠ i' →
      ∃ (g : V →ₗ[𝒪] V) (b' : B'), b' ∉ S'.𝔪 j' ∧ (∀ v : V, f (g v) = b' • f v) ∧
        (∀ w ∈ W, g w ∈ W) ∧ (∀ k : ℕ, ∃ n : ℕ, ∀ w ∈ W, (g ^ n) w ∈ (I ^ k • ⊤ : Submodule 𝒪 V))) :
    ∀ w ∈ W, f w ∈ cornerSubmodule (M := V') (S'.e i') := by p2m_exact_reverting @_root_.P2MW.S_IharaLemma_map_le_cornerSubmodule_of_forall_ne_exists_intertwining.solution
