import Mathlib.RingTheory.Ideal.Operations
import Definitions.Def_IharaLemma_IdempotentSplitting
import P2M.Util
import P2M.Sol.S_IharaLemma_eq_zero_of_mem_cornerSubmodule_of_intertwining_nilpotent

set_option autoImplicit false

open IharaLemma

theorem IharaLemma.eq_zero_of_mem_cornerSubmodule_of_intertwining_nilpotent
    {𝒪 : Type} [CommRing 𝒪] {B' : Type} [CommRing B'] [Algebra 𝒪 B']
    {V : Type} [AddCommGroup V] [Module 𝒪 V]
    {V' : Type} [AddCommGroup V'] [Module 𝒪 V'] [Module B' V'] [IsScalarTower 𝒪 B' V']
    (f : V' →ₗ[𝒪] V) (S' : IdempotentSplitting B') (i' : Fin S'.n)
    (t' : B') (ht' : t' ∉ S'.𝔪 i') (β : V →ₗ[𝒪] V) (hf : ∀ v' : V', f (t' • v') = β (f v'))
    (I : Ideal 𝒪) (hβ : ∀ k : ℕ, ∃ n : ℕ, ∀ v : V, (β ^ n) v ∈ (I ^ k • ⊤ : Submodule 𝒪 V))
    (hsep : ∀ v : V, (∀ k : ℕ, v ∈ (I ^ k • ⊤ : Submodule 𝒪 V)) → v = 0) :
    ∀ v' ∈ cornerSubmodule (M := V') (S'.e i'), f v' = 0 := by p2m_exact_reverting @_root_.P2MW.S_IharaLemma_eq_zero_of_mem_cornerSubmodule_of_intertwining_nilpotent.solution
