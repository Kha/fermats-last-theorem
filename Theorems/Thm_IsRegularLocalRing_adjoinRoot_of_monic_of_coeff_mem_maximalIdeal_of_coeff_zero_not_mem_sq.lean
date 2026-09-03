import Mathlib
import P2M.Util
import P2M.Sol.S_IsRegularLocalRing_adjoinRoot_of_monic_of_coeff_mem_maximalIdeal_of_coeff_zero_not_mem_sq

set_option autoImplicit false

open IsLocalRing Polynomial

theorem IsRegularLocalRing.adjoinRoot_of_monic_of_coeff_mem_maximalIdeal_of_coeff_zero_not_mem_sq
    (S : Type*) [CommRing S] [IsRegularLocalRing S]
    (g : S[X]) (hg : g.Monic) (hn : 1 ≤ g.natDegree)
    (hcoeff : ∀ i < g.natDegree, g.coeff i ∈ maximalIdeal S)
    (h0 : g.coeff 0 ∉ maximalIdeal S ^ 2) :
    IsRegularLocalRing (AdjoinRoot g) ∧ ringKrullDim (AdjoinRoot g) = ringKrullDim S := by p2m_exact_reverting @_root_.P2MW.S_IsRegularLocalRing_adjoinRoot_of_monic_of_coeff_mem_maximalIdeal_of_coeff_zero_not_mem_sq.solution
