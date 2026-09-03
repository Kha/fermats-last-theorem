import Mathlib
import P2M.Util
import P2M.Sol.S_HomogeneousIdeal_exists_homogeneous_pos_mem_forall_notMem

universe u v

theorem HomogeneousIdeal.exists_homogeneous_pos_mem_forall_notMem
    {A : Type u} {σ : Type v} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] {𝒜 : ℕ → σ} [GradedRing 𝒜]
    (I : HomogeneousIdeal 𝒜) (hirr : I ≤ HomogeneousIdeal.irrelevant 𝒜)
    (t : Finset (HomogeneousIdeal 𝒜)) (hprime : ∀ p ∈ t, p.toIdeal.IsPrime) (havoid : ∀ p ∈ t, ¬ I ≤ p) :
    ∃ (n : ℕ) (x : A), 0 < n ∧ x ∈ 𝒜 n ∧ x ∈ I ∧ ∀ p ∈ t, x ∉ p := by p2m_exact_reverting @_root_.P2MW.S_HomogeneousIdeal_exists_homogeneous_pos_mem_forall_notMem.solution
