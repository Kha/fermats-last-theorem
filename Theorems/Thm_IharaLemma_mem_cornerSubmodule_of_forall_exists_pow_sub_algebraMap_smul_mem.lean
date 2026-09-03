import Definitions.Def_IharaLemma_IdempotentSplitting
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.Ideal.Maps
import P2M.Util
import P2M.Sol.S_IharaLemma_mem_cornerSubmodule_of_forall_exists_pow_sub_algebraMap_smul_mem

set_option autoImplicit false

open IsLocalRing IharaLemma

theorem IharaLemma.mem_cornerSubmodule_of_forall_exists_pow_sub_algebraMap_smul_mem
    {𝒪 : Type} [CommRing 𝒪] [IsLocalRing 𝒪]
    {B : Type} [CommRing B] [Algebra 𝒪 B]
    {V : Type} [AddCommGroup V] [Module 𝒪 V] [Module B V] [IsScalarTower 𝒪 B V]
    (hsep : ∀ v : V, (∀ k : ℕ, v ∈ ((maximalIdeal 𝒪) ^ k • ⊤ : Submodule 𝒪 V)) → v = 0)
    (S : IdempotentSplitting B) (i : Fin S.n)
    (G : Set B) (hG : Algebra.adjoin 𝒪 G = ⊤)
    (c : B → 𝒪) (hc : ∀ g ∈ G, g - algebraMap 𝒪 B (c g) ∈ S.𝔪 i)
    (v : V)
    (hv : ∀ g ∈ G, ∀ k : ℕ, ∃ n : ℕ,
      ((g - algebraMap 𝒪 B (c g)) ^ n) • v ∈ ((maximalIdeal 𝒪) ^ k • ⊤ : Submodule 𝒪 V)) :
    v ∈ cornerSubmodule (M := V) (S.e i) := by p2m_exact_reverting @_root_.P2MW.S_IharaLemma_mem_cornerSubmodule_of_forall_exists_pow_sub_algebraMap_smul_mem.solution
