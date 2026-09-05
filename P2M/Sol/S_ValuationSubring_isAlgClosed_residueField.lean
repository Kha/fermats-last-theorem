module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
import P2M.Sol.S_ValuationSubring_exists_root_mem_of_monic
import P2M.Util
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

namespace P2MW.S_ValuationSubring_isAlgClosed_residueField

set_option autoImplicit false

open IsLocalRing

theorem solution {K : Type*} [Field K] [IsAlgClosed K] (A : ValuationSubring K) :
    IsAlgClosed (IsLocalRing.ResidueField A) := by
  apply IsAlgClosed.of_exists_root
  intro p hmonic hirr
  have hlift : p ∈ Polynomial.lifts (residue A) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    exact fun n => residue_surjective _
  obtain ⟨f, hmap, hdeg, hf⟩ := Polynomial.lifts_and_degree_eq_and_monic hlift hmonic
  have hd : f.natDegree ≠ 0 := by
    rw [Polynomial.natDegree_eq_of_degree_eq hdeg]
    exact hirr.natDegree_pos.ne'
  obtain ⟨x, hx⟩ := ValuationSubring.exists_root_mem_of_monic A f hf hd
  refine ⟨residue A x, ?_⟩
  have hx0 : f.eval x = 0 := by
    have h1 : (algebraMap A K) (f.eval x) = 0 := by
      rw [← hx, Polynomial.aeval_def]
      exact (Polynomial.eval₂_at_apply (algebraMap A K) x).symm
    exact Subtype.coe_injective (by simpa using h1)
  rw [← hmap, Polynomial.eval_map, Polynomial.eval₂_at_apply, hx0, map_zero]
end S_ValuationSubring_isAlgClosed_residueField
end P2MW

public section
theorem ValuationSubring.isAlgClosed_residueField {K : Type*} [Field K] [IsAlgClosed K]
    (A : ValuationSubring K) : IsAlgClosed (IsLocalRing.ResidueField A) := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_isAlgClosed_residueField.solution
end
