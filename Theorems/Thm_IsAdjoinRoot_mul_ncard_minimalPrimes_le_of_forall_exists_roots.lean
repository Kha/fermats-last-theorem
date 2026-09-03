import Mathlib
import P2M.Util
import P2M.Sol.S_IsAdjoinRoot_mul_ncard_minimalPrimes_le_of_forall_exists_roots

set_option autoImplicit false

theorem IsAdjoinRoot.mul_ncard_minimalPrimes_le_of_forall_exists_roots
    (R S : Type) [CommRing R] [CommRing S] [Algebra R S]
    (f : Polynomial R) (hf : f.Monic) (hS : IsAdjoinRoot S f) (n : ℕ)
    (hroots : ∀ 𝔭 ∈ minimalPrimes R, ∃ s : Finset (FractionRing (R ⧸ 𝔭)), n ≤ s.card ∧
      ∀ z ∈ s, (f.map (algebraMap R (FractionRing (R ⧸ 𝔭)))).IsRoot z)
    (hfin : (minimalPrimes S).Finite) :
    n * (minimalPrimes R).ncard ≤ (minimalPrimes S).ncard := by p2m_exact_reverting @_root_.P2MW.S_IsAdjoinRoot_mul_ncard_minimalPrimes_le_of_forall_exists_roots.solution
