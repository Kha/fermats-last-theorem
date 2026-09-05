module

public import Definitions.Def_WeierstrassCurve_HasseInvariant
import P2M.Sol.S_WeierstrassCurve_hasseInvariant_variableChange
import P2M.Util
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.EllipticCurve.IsomOfJ
import Mathlib.AlgebraicGeometry.EllipticCurve.ModelsWithJ
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.Geometry.Euclidean.Altitude
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

namespace P2MW.S_ModularCurve_zero_mem_ssJSetHasse_iff

set_option autoImplicit false

p2m_open "Polynomial P2MW.S_ModularCurve_zero_mem_ssJSetHasse_iff.Polynomial"

noncomputable section

namespace Polynomial
p2m_export "Polynomial" "C X coeff C_pow coeff_mul_C coeff_C_mul finsetSum_coeff coeff_X_pow ring"
p2m_open "Polynomial"

theorem coeff_C_mul_X_pow_add_C_pow' {R : Type*} [CommRing R] (a b : R) (d m n : ℕ) :
    ((C a * X ^ d + C b) ^ m).coeff n
      = ∑ k ∈ Finset.range (m + 1), if n = d * k then a ^ k * b ^ (m - k) * (m.choose k) else 0 := by
  rw [add_pow, finsetSum_coeff]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_pow, ← C_pow, ← C_pow, ← pow_mul, ← map_natCast C, coeff_mul_C, coeff_mul_C,
    coeff_C_mul, coeff_X_pow]
  split_ifs <;> ring

end Polynomial

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "ofJ0 b₂ twoTorsionPolynomial ofJ0_Δ exists_variableChange_of_j_eq ofJ0_c₄ b₆ VariableChange j b₄ hasseInvariant hasseInvariant_variableChange"
p2m_open "WeierstrassCurve"

theorem hasseInvariant_variableChange_eq_zero_iff' {K : Type*} [Field K] {q : ℕ} [Fact q.Prime]
    [CharP K q] (W : WeierstrassCurve K) (v : VariableChange K) :
    (v • W).hasseInvariant q = 0 ↔ W.hasseInvariant q = 0 := by
  rw [hasseInvariant_variableChange, mul_eq_zero, or_iff_right]
  exact pow_ne_zero _ (v.u⁻¹).ne_zero

end WeierstrassCurve

namespace ModularCurve
p2m_export "ModularCurve" "ssJSetHasse"
p2m_open "ModularCurve"

p2m_open "WeierstrassCurve P2MW.S_ModularCurve_zero_mem_ssJSetHasse_iff.WeierstrassCurve"

theorem two_ne_zero_of_charP_of_ne_two' (K : Type*) [Field K] {q : ℕ} [hp : Fact q.Prime]
    [CharP K q] (hq2 : q ≠ 2) : (2 : K) ≠ 0 := by
  have : ((2 : ℕ) : K) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff K q]
    intro h
    exact hq2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp h)
  simpa using this

theorem natCast_choose_ne_zero_of_lt' (K : Type*) [Field K] {q : ℕ} [hp : Fact q.Prime] [CharP K q]
    {m k : ℕ} (hm : m < q) (hk : k ≤ m) : ((m.choose k : ℕ) : K) ≠ 0 := by
  rw [Ne, CharP.cast_eq_zero_iff K q]
  intro hd
  have h1 : m.choose k ∣ m.factorial :=
    ⟨k.factorial * (m - k).factorial, by rw [← mul_assoc, Nat.choose_mul_factorial_mul_factorial hk]⟩
  have := (hp.out.dvd_factorial).mp (hd.trans h1)
  omega

theorem mem_ssJSetHasse_iff_of_j_eq' {K : Type*} [Field K] [IsAlgClosed K] (q : ℕ) [Fact q.Prime]
    [CharP K q] (W : WeierstrassCurve K) [W.IsElliptic] {j : K} (hW : W.j = j) :
    j ∈ ssJSetHasse q K ↔ W.hasseInvariant q = 0 := by
  constructor
  · intro h
    exact h W hW
  · intro h
    rw [ssJSetHasse, Set.mem_setOf_eq]
    intro W' _ hW'
    haveI := IsSepClosed.of_isAlgClosed K
    obtain ⟨v, rfl⟩ := exists_variableChange_of_j_eq W W' (by rw [hW, hW'])
    rwa [hasseInvariant_variableChange_eq_zero_iff']

theorem twoTorsionPolynomial_ofJ0_toPoly' (K : Type*) [Field K] :
    (ofJ0 K).twoTorsionPolynomial.toPoly = C 4 * X ^ 3 + C 1 := by
  have hb2 : (ofJ0 K).b₂ = 0 := by simp [ofJ0, b₂]
  have hb4 : (ofJ0 K).b₄ = 0 := by simp [ofJ0, b₄]
  have hb6 : (ofJ0 K).b₆ = 1 := by simp [ofJ0, b₆]
  simp only [twoTorsionPolynomial, Cubic.toPoly, hb2, hb4, hb6, mul_zero, map_zero, zero_mul,
    add_zero, map_one]

theorem hasseInvariant_ofJ0_eq_zero_iff' (K : Type*) [Field K] (q : ℕ) [hp : Fact q.Prime]
    [CharP K q] (hq2 : q ≠ 2) :
    (ofJ0 K).hasseInvariant q = 0 ↔ ¬ 3 ∣ (q - 1) / 2 := by
  obtain ⟨m, hm⟩ := hp.out.odd_of_ne_two hq2
  have hm1 : (q - 1) / 2 = m := by omega
  have hm2 : q - 1 = 2 * m := by omega
  have hmq : m < q := by omega
  have h4 : (4 : K) ≠ 0 := by
    rw [show (4 : K) = 2 ^ 2 by norm_num]
    exact pow_ne_zero _ (two_ne_zero_of_charP_of_ne_two' K hq2)
  rw [hasseInvariant, hm1, hm2, twoTorsionPolynomial_ofJ0_toPoly', coeff_C_mul_X_pow_add_C_pow']
  by_cases h3 : 3 ∣ m
  · obtain ⟨a, rfl⟩ := h3
    rw [Finset.sum_eq_single (2 * a)]
    · rw [if_pos (by ring)]
      refine iff_of_false ?_ (fun h => h (dvd_mul_right 3 a))
      simp only [one_pow, mul_one]
      exact mul_ne_zero (pow_ne_zero _ h4) (natCast_choose_ne_zero_of_lt' K hmq (by omega))
    · intro k _ hk
      exact if_neg (by omega)
    · intro h
      exact absurd (Finset.mem_range.mpr (by omega)) h
  · rw [Finset.sum_eq_zero (fun k _ => if_neg (by omega))]
    exact iff_of_true rfl h3

theorem isElliptic_ofJ0_of_three_ne_zero' (K : Type*) [Field K] (h3 : (3 : K) ≠ 0) :
    (ofJ0 K).IsElliptic := by
  refine ⟨?_⟩
  rw [ofJ0_Δ, isUnit_iff_ne_zero, neg_ne_zero, show (27 : K) = 3 ^ 3 by norm_num]
  exact pow_ne_zero _ h3

theorem three_ne_zero_of_charP_of_five_le' (K : Type*) [Field K] {q : ℕ} [hp : Fact q.Prime]
    [CharP K q] (hq : 5 ≤ q) : (3 : K) ≠ 0 := by
  have : ((3 : ℕ) : K) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff K q]
    intro h
    have := (Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_three).mp h
    omega
  simpa using this

theorem zero_mem_ssJSetHasse_iff' (q : ℕ) [hp : Fact q.Prime] (hq : 5 ≤ q) (K : Type*) [Field K]
    [IsAlgClosed K] [CharP K q] : (0 : K) ∈ ssJSetHasse q K ↔ q % 3 = 2 := by
  have hq2 : q ≠ 2 := by omega
  haveI := isElliptic_ofJ0_of_three_ne_zero' K (three_ne_zero_of_charP_of_five_le' K hq)
  have hj : (ofJ0 K).j = 0 := by
    rw [j, ofJ0_c₄]; ring
  rw [mem_ssJSetHasse_iff_of_j_eq' q (ofJ0 K) hj, hasseInvariant_ofJ0_eq_zero_iff' K q hq2]
  have h3q : ¬ 3 ∣ q := fun h => by
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp.out).mp h; omega
  obtain ⟨m, hm⟩ := hp.out.odd_of_ne_two hq2
  have hm1 : (q - 1) / 2 = m := by omega
  rw [hm1]
  omega

end ModularCurve

end

p2m_open "ModularCurve P2MW.S_ModularCurve_zero_mem_ssJSetHasse_iff.ModularCurve"

theorem solution (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (K : Type*) [Field K]
    [IsAlgClosed K] [CharP K q] : (0 : K) ∈ ssJSetHasse q K ↔ q % 3 = 2 :=
  ModularCurve.zero_mem_ssJSetHasse_iff' q hq K
end S_ModularCurve_zero_mem_ssJSetHasse_iff
end P2MW

public section
open ModularCurve
theorem ModularCurve.zero_mem_ssJSetHasse_iff (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (K : Type*) [Field K]
    [IsAlgClosed K] [CharP K q] : (0 : K) ∈ ssJSetHasse q K ↔ q % 3 = 2 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_zero_mem_ssJSetHasse_iff.solution
end
