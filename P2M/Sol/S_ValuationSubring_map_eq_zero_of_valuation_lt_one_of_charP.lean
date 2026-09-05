module

public import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.ENatToNat
import Std.Tactic.BVDecide.Normalize.Prop
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

namespace P2MW.S_ValuationSubring_map_eq_zero_of_valuation_lt_one_of_charP

set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

open Polynomial

namespace S12R4

theorem map_ne_zero_of_isPrimitive {Q : ℤ[X]} (hQ : Q.IsPrimitive) (ℓ : ℕ) [hℓ : Fact ℓ.Prime] :
    Q.map (Int.castRingHom (ZMod ℓ)) ≠ 0 := by
  intro h
  have hdvd : C (ℓ : ℤ) ∣ Q := by
    rw [C_dvd_iff_dvd_coeff]
    intro n
    have hn : ((Q.coeff n : ℤ) : ZMod ℓ) = 0 := by
      have := congrArg (fun p => p.coeff n) h
      simpa [coeff_map] using this
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ ℓ).mp hn
  have hunit := hQ _ hdvd
  rw [Int.isUnit_iff_natAbs_eq, Int.natAbs_natCast] at hunit
  exact hℓ.out.one_lt.ne' hunit

theorem exists_isPrimitive_aeval_eq_zero (A : ValuationSubring (AlgebraicClosure ℚ)) (a : A) :
    ∃ Q : ℤ[X], Q.IsPrimitive ∧ aeval a Q = 0 := by
  have halg : IsAlgebraic ℤ (a : AlgebraicClosure ℚ) :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ (AlgebraicClosure ℚ)).mpr
      ((AlgebraicClosure.isAlgebraic ℚ).isAlgebraic (a : AlgebraicClosure ℚ))
  obtain ⟨P, hP0, hP⟩ := halg
  refine ⟨P.primPart, P.isPrimitive_primPart, ?_⟩
  have hc : (P.content : AlgebraicClosure ℚ) ≠ 0 := by
    exact_mod_cast (mt content_eq_zero_iff.mp hP0)
  have hprim : aeval (a : AlgebraicClosure ℚ) P.primPart = 0 := by
    rw [P.eq_C_content_mul_primPart, map_mul, aeval_C] at hP
    simpa [hc] using hP

  apply Subtype.val_injective
  let f : A →ₐ[ℤ] AlgebraicClosure ℚ := (A.toSubring.subtype).toIntAlgHom
  have hf : ∀ x : A, f x = (x : AlgebraicClosure ℚ) := fun x => rfl
  show (aeval a P.primPart : A).val = (0 : A).val
  rw [← hf, ← hf, ← Polynomial.aeval_algHom_apply, hf, hprim]
  rfl

end S12R4

theorem solution
    (A : ValuationSubring (AlgebraicClosure ℚ)) (ℓ : ℕ) [Fact ℓ.Prime] (hA : A.LiesOverPrime ℓ)
    {k : Type*} [Field k] [CharP k ℓ] (red : ↥A →+* k)
    (τ : ↥A) (hτ : A.valuation (τ : AlgebraicClosure ℚ) < 1) :
    red τ = 0 := by
  classical
  haveI hprime : (RingHom.ker red).IsPrime := RingHom.ker_isPrime red
  haveI : IsDomain (A ⧸ RingHom.ker red) := Ideal.Quotient.isDomain _

  have hℓ : ((ℓ : ℕ) : A ⧸ RingHom.ker red) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk (RingHom.ker red)), Ideal.Quotient.eq_zero_iff_mem,
      RingHom.mem_ker, map_natCast]
    exact CharP.cast_eq_zero k ℓ
  haveI : CharP (A ⧸ RingHom.ker red) ℓ := (CharP.charP_iff_prime_eq_zero Fact.out).mpr hℓ
  letI : Algebra (ZMod ℓ) (A ⧸ RingHom.ker red) := ZMod.algebra _ ℓ

  haveI halg : Algebra.IsAlgebraic (ZMod ℓ) (A ⧸ RingHom.ker red) := by
    refine ⟨fun x => ?_⟩
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨Q, hQ, haQ⟩ := S12R4.exists_isPrimitive_aeval_eq_zero A a
    refine ⟨Q.map (Int.castRingHom (ZMod ℓ)), S12R4.map_ne_zero_of_isPrimitive hQ ℓ, ?_⟩
    rw [aeval_def, eval₂_map,
      show (algebraMap (ZMod ℓ) (A ⧸ RingHom.ker red)).comp (Int.castRingHom (ZMod ℓ))
        = algebraMap ℤ (A ⧸ RingHom.ker red) from RingHom.ext_int _ _,
      ← aeval_def,
      show (Ideal.Quotient.mk (RingHom.ker red)) a = Ideal.Quotient.mkₐ ℤ (RingHom.ker red) a from rfl,
      aeval_algHom_apply, haQ, map_zero]
  haveI : Algebra.IsIntegral (ZMod ℓ) (A ⧸ RingHom.ker red) := Algebra.isAlgebraic_iff_isIntegral.mp halg

  have hfield : IsField (A ⧸ RingHom.ker red) :=
    isField_of_isIntegral_of_isField' (Field.toIsField (ZMod ℓ))
  have hmax : (RingHom.ker red).IsMaximal := Ideal.Quotient.maximal_of_isField _ hfield
  have hker : RingHom.ker red = IsLocalRing.maximalIdeal A := IsLocalRing.eq_maximalIdeal hmax
  have hτ' : τ ∈ IsLocalRing.maximalIdeal A := (A.valuation_lt_one_iff τ).mpr hτ
  rw [← hker, RingHom.mem_ker] at hτ'
  exact hτ'
end S_ValuationSubring_map_eq_zero_of_valuation_lt_one_of_charP
end P2MW

public section
theorem ValuationSubring.map_eq_zero_of_valuation_lt_one_of_charP
    (A : ValuationSubring (AlgebraicClosure ℚ)) (ℓ : ℕ) [Fact ℓ.Prime] (hA : A.LiesOverPrime ℓ)
    {k : Type*} [Field k] [CharP k ℓ] (red : ↥A →+* k)
    (τ : ↥A) (hτ : A.valuation (τ : AlgebraicClosure ℚ) < 1) :
    red τ = 0 := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_map_eq_zero_of_valuation_lt_one_of_charP.solution
end
