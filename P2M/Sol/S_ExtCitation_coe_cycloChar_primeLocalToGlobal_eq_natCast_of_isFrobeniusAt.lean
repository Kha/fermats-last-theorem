import Mathlib
import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Definitions.Def_ExtCitation_InertiaKummerCharacter
import P2M.Util
namespace P2MW.S_ExtCitation_coe_cycloChar_primeLocalToGlobal_eq_natCast_of_isFrobeniusAt

set_option autoImplicit false
open CategoryTheory Module groupCohomology ExtCitation

theorem solution
    (p : ℕ) [Fact p.Prime] (q : Nat.Primes) (hqp : (q : ℕ) ≠ p)
    {φ : primeLocalGaloisGroup q}
    (hφ : (primeLocalPlace q).IsFrobeniusAt (primeLocalToGlobal q φ) q) :
    ((cycloChar p (primeLocalToGlobal q φ) : (ZMod p)ˣ) : ZMod p) = ((q : ℕ) : ZMod p) := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  symm
  refine modularCyclotomicCharacter.unique (AlgebraicClosure ℚ) (card_rootsOfUnity_eq_self p)
    (primeLocalToGlobal q φ : AlgebraicClosure ℚ ≃+* AlgebraicClosure ℚ) (fun t ht => ?_)
  have ht' : ((t : AlgebraicClosure ℚ)) ^ p = 1 := by
    rw [mem_rootsOfUnity] at ht
    rw [← Units.val_pow_eq_pow_val, ht, Units.val_one]
  rw [ZMod.val_natCast]
  change primeLocalToGlobal q φ (t : AlgebraicClosure ℚ) = _
  rw [frobenius_smul_eq_pow_of_pow_eq_one q hφ (not_dvd_of_ne p q hqp) ht']
  conv_lhs => rw [← Nat.mod_add_div (q : ℕ) p, pow_add, pow_mul, ht', one_pow, mul_one]
