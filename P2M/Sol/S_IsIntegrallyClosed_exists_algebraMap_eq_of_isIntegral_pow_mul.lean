module

import P2M.Util
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Altitude
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Sheaves.Init

namespace P2MW.S_IsIntegrallyClosed_exists_algebraMap_eq_of_isIntegral_pow_mul

theorem solution
    {R : Type*} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
    (t : R) (ht0 : t ≠ 0) (ht : (Ideal.span {t}).IsPrime)
    (f : K) (hv : ∃ r s : R, s ∉ Ideal.span {t} ∧ f * algebraMap R K s = algebraMap R K r)
    (hint : ∃ n : ℕ, IsIntegral R (algebraMap R K t ^ n * f)) :
    ∃ r : R, algebraMap R K r = f := by
  obtain ⟨n, hn⟩ := hint
  obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.mp hn
  obtain ⟨r, s, hs, hfs⟩ := hv
  have htK : algebraMap R K t ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr ht0
  have hprime : Prime t := (Ideal.span_singleton_prime ht0).mp ht
  have hts : ¬ t ∣ s := fun h => hs (Ideal.mem_span_singleton.mpr h)

  have has : a * s = t ^ n * r := by
    apply IsFractionRing.injective R K
    rw [map_mul, map_mul, map_pow, ha, mul_assoc, hfs]

  obtain ⟨c, hc⟩ := hprime.pow_dvd_of_dvd_mul_right n hts ⟨r, has⟩
  refine ⟨c, mul_left_cancel₀ (pow_ne_zero n htK) ?_⟩
  rw [← ha, hc, map_mul, map_pow]
end S_IsIntegrallyClosed_exists_algebraMap_eq_of_isIntegral_pow_mul
end P2MW

public section
theorem IsIntegrallyClosed.exists_algebraMap_eq_of_isIntegral_pow_mul
    {R : Type*} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
    (t : R) (ht0 : t ≠ 0) (ht : (Ideal.span {t}).IsPrime)
    (f : K) (hv : ∃ r s : R, s ∉ Ideal.span {t} ∧ f * algebraMap R K s = algebraMap R K r)
    (hint : ∃ n : ℕ, IsIntegral R (algebraMap R K t ^ n * f)) :
    ∃ r : R, algebraMap R K r = f := by p2m_exact_reverting @_root_.P2MW.S_IsIntegrallyClosed_exists_algebraMap_eq_of_isIntegral_pow_mul.solution
end
