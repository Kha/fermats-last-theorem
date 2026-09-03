import Mathlib
import P2M.Util
import P2M.Sol.S_HopfAlgebra_exists_forall_pow_pow_eq_algebraMap_counit_of_isLocalRing_zmodp

set_option autoImplicit false

theorem HopfAlgebra.exists_forall_pow_pow_eq_algebraMap_counit_of_isLocalRing_zmodp
    (p : ℕ) [Fact p.Prime]
    (B : Type) [CommRing B] [HopfAlgebra (ZMod p) B] [Module.Finite (ZMod p) B]
    (hB : IsLocalRing B) :
    ∃ N : ℕ, 0 < N ∧ ∀ x : B, x ^ p ^ N = algebraMap (ZMod p) B (Coalgebra.counit (R := ZMod p) x) := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_exists_forall_pow_pow_eq_algebraMap_counit_of_isLocalRing_zmodp.solution
