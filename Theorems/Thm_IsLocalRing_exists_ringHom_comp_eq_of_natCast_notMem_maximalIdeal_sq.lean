import Mathlib
import P2M.Util
import P2M.Sol.S_IsLocalRing_exists_ringHom_comp_eq_of_natCast_notMem_maximalIdeal_sq

set_option autoImplicit false

universe u v w

open IsLocalRing

theorem IsLocalRing.exists_ringHom_comp_eq_of_natCast_notMem_maximalIdeal_sq
    {q : ℕ} [Fact q.Prime] {S : Type u} [CommRing S] [IsLocalRing S]
    [Finite (ResidueField S)] [CharP (ResidueField S) q]
    (hq : ((q : ℕ) : S) ∉ maximalIdeal S ^ 2)
    {D : Type v} [CommRing D] [IsLocalRing D] (hD : maximalIdeal D ^ 2 = ⊥)
    {K : Type w} [Field K] (πD : D →+* K) (hπD : Function.Surjective πD)
    (x : S →+* K) (hx : RingHom.ker x = maximalIdeal S) :
    ∃ ψ : S →+* D, πD.comp ψ = x := by p2m_exact_reverting @_root_.P2MW.S_IsLocalRing_exists_ringHom_comp_eq_of_natCast_notMem_maximalIdeal_sq.solution
