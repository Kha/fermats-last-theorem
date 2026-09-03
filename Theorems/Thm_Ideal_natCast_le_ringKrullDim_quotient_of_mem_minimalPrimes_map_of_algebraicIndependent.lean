import Mathlib
import P2M.Util
import P2M.Sol.S_Ideal_natCast_le_ringKrullDim_quotient_of_mem_minimalPrimes_map_of_algebraicIndependent

set_option autoImplicit false

universe u v w

theorem Ideal.natCast_le_ringKrullDim_quotient_of_mem_minimalPrimes_map_of_algebraicIndependent
    (k : Type u) [Field k] {R : Type v} {C : Type w} [CommRing R] [IsDomain R] [Algebra k R]
    [Algebra.FiniteType k R] [CommRing C] [IsDomain C] [Algebra k C] [Algebra R C]
    [IsScalarTower k R C] [Algebra.FiniteType R C]
    {d : ℕ} (z : Fin d → C) (hz : AlgebraicIndependent R z) (r : R) (hr : r ≠ 0)
    (hint : ∀ c : C, ∃ n : ℕ, IsIntegral (Algebra.adjoin R (Set.range z)) (r ^ n • c))
    (p : Ideal R) [p.IsMaximal] (hrp : r ∉ p)
    (Q : Ideal C) (hQ : Q ∈ (p.map (algebraMap R C)).minimalPrimes) :
    (d : WithBot ℕ∞) ≤ ringKrullDim (C ⧸ Q) := by p2m_exact_reverting @_root_.P2MW.S_Ideal_natCast_le_ringKrullDim_quotient_of_mem_minimalPrimes_map_of_algebraicIndependent.solution
