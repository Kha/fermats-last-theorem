import Mathlib.RingTheory.LocalRing.ResidueField.Defs
import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Degree.Defs
import P2M.Util
import P2M.Sol.S_IsLocalRing_exists_pow_pow_eq_one_of_isRoot_map_of_map_residue_eq_X_sub_one_pow

set_option autoImplicit false

open Polynomial

theorem IsLocalRing.exists_pow_pow_eq_one_of_isRoot_map_of_map_residue_eq_X_sub_one_pow
    {R : Type} [CommRing R] [IsLocalRing R] (p : ℕ) [Fact p.Prime] [CharP (IsLocalRing.ResidueField R) p]
    (P : R[X]) (hP : P.map (IsLocalRing.residue R) = (X - 1) ^ P.natDegree)
    {S : Type} [CommRing S] (j : R →+* S) (ζ : S) (hζ : (P.map j).IsRoot ζ)
    {d : ℕ} (hd : 0 < d) (hζd : ζ ^ d = 1) :
    ∃ n : ℕ, ζ ^ p ^ n = 1 := by p2m_exact_reverting @_root_.P2MW.S_IsLocalRing_exists_pow_pow_eq_one_of_isRoot_map_of_map_residue_eq_X_sub_one_pow.solution
