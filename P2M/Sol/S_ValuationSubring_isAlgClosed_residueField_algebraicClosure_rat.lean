module

import P2M.Util
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.RingTheory.Valuation.ValuationSubring
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.LocalSubring
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

namespace P2MW.S_ValuationSubring_isAlgClosed_residueField_algebraicClosure_rat

open IsLocalRing Polynomial

theorem solution (A : ValuationSubring (AlgebraicClosure ℚ)) :
    IsAlgClosed (ResidueField A) := by
  refine IsAlgClosed.of_exists_root _ fun f hfm hfi => ?_

  have hsurj : Function.Surjective (residue A) := Ideal.Quotient.mk_surjective
  obtain ⟨F0, hF0⟩ := Polynomial.map_surjective _ hsurj f
  obtain ⟨F, hFmap, -, hFm⟩ :=
    Polynomial.lifts_and_degree_eq_and_monic ((Polynomial.mem_lifts f).mpr ⟨F0, hF0⟩) hfm

  let G := F.map (algebraMap A (AlgebraicClosure ℚ))
  have hGdeg : G.degree ≠ 0 := by
    have : G.degree = f.degree := by
      rw [show G = F.map _ from rfl, hFm.degree_map, ← hFmap, hFm.degree_map]
    rw [this]; exact (Polynomial.degree_pos_of_irreducible hfi).ne'
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_root G hGdeg

  have hint : IsIntegral A α := ⟨F, hFm, by rwa [← Polynomial.eval_map]⟩
  obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint

  refine ⟨residue A a, ?_⟩
  have hFa : F.eval a = 0 := by
    apply IsFractionRing.injective A (AlgebraicClosure ℚ)
    rw [map_zero, ← Polynomial.eval₂_at_apply, ← Polynomial.eval_map, ha]; exact hα
  rw [← hFmap, Polynomial.eval_map, Polynomial.eval₂_at_apply, hFa, map_zero]
end S_ValuationSubring_isAlgClosed_residueField_algebraicClosure_rat
end P2MW

public section
open IsLocalRing
theorem ValuationSubring.isAlgClosed_residueField_algebraicClosure_rat
    (A : ValuationSubring (AlgebraicClosure ℚ)) :
    IsAlgClosed (ResidueField A) := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_isAlgClosed_residueField_algebraicClosure_rat.solution
end
