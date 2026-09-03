import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.Finiteness.Defs
import Definitions.Def_IharaLemma_IdempotentSplitting
import P2M.Util
import P2M.Sol.S_IharaLemma_exists_pow_smul_corner_mem_maximalIdeal_smul

set_option autoImplicit false

open IharaLemma

theorem IharaLemma.exists_pow_smul_corner_mem_maximalIdeal_smul
    {𝒪 : Type} [CommRing 𝒪] [IsLocalRing 𝒪] {B : Type} [CommRing B] [Algebra 𝒪 B] [Module.Finite 𝒪 B]
    (S : IdempotentSplitting B) (i : Fin S.n) (b : B) (hb : b ∈ S.𝔪 i)
    {V : Type} [AddCommGroup V] [Module 𝒪 V] [Module B V] [IsScalarTower 𝒪 B V] (k : ℕ) :
    ∃ n : ℕ, ∀ v : V, v ∈ cornerSubmodule (M := V) (S.e i) →
      (b ^ n) • v ∈ ((IsLocalRing.maximalIdeal 𝒪) ^ k • ⊤ : Submodule 𝒪 V) := by p2m_exact_reverting @_root_.P2MW.S_IharaLemma_exists_pow_smul_corner_mem_maximalIdeal_smul.solution
