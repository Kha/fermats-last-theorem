import Definitions.Def_GaloisRep_TameCharacter
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Mathlib.FieldTheory.Minpoly.Basic
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Algebra.Group.Submonoid.BigOperators
import Mathlib.Algebra.GroupWithZero.Units.Lemmas
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import P2M.Util
namespace P2MW.S_ValuationSubring_residue_eq_one_of_pow_prime_pow_eq_one

namespace DichTameRows

open ValuationSubring
open scoped Pointwise

variable (P : ValuationSubring (AlgebraicClosure ℚ))

private theorem residue_eq_one_of_pow_prime_pow_eq_one {p : ℕ} (hp : p.Prime) (hP : P.LiesOverPrime p)
    {ζ : AlgebraicClosure ℚ} {n : ℕ} (hζ : ζ ^ p ^ n = 1) (hζP : ζ ∈ P) :
    IsLocalRing.residue P ⟨ζ, hζP⟩ = 1 := by
  haveI := Fact.mk hp
  have hP' : ((p : ℕ) : AlgebraicClosure ℚ) ∈ P.nonunits := hP
  have hpP : ((p : ℕ) : P) ∈ IsLocalRing.maximalIdeal P := by
    rw [← coe_mem_nonunits_iff, SubringClass.coe_natCast]
    exact hP'
  haveI hchar : CharP (IsLocalRing.ResidueField P) p := by
    rw [CharP.charP_iff_prime_eq_zero hp, ← map_natCast (IsLocalRing.residue P), IsLocalRing.residue_eq_zero_iff]
    exact hpP
  have hx : (⟨ζ, hζP⟩ : P) ^ p ^ n = 1 := Subtype.ext (by simp only [SubmonoidClass.coe_pow]; exact hζ)
  have hrp : IsLocalRing.residue P ⟨ζ, hζP⟩ ^ p ^ n = 1 := by
    rw [← map_pow, hx, map_one]
  have h0 : (IsLocalRing.residue P ⟨ζ, hζP⟩ - 1) ^ p ^ n = 0 := by
    rw [sub_pow_char_pow, hrp, one_pow, sub_self]
  exact sub_eq_zero.mp ((pow_eq_zero_iff (pow_ne_zero n hp.ne_zero)).mp h0)

end DichTameRows

theorem solution
    (P : ValuationSubring (AlgebraicClosure ℚ)) {p : ℕ} (hp : p.Prime) (hP : P.LiesOverPrime p)
    {ζ : AlgebraicClosure ℚ} {n : ℕ} (hζ : ζ ^ p ^ n = 1) (hζP : ζ ∈ P) :
    IsLocalRing.residue P ⟨ζ, hζP⟩ = 1 :=
  DichTameRows.residue_eq_one_of_pow_prime_pow_eq_one P hp hP hζ hζP
