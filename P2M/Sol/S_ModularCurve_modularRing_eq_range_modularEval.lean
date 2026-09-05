module

public import Definitions.Def_ModularCurve_NodeLocalized
import P2M.Util
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

namespace P2MW.S_ModularCurve_modularRing_eq_range_modularEval

set_option autoImplicit false

open ModularCurve ModularCurve.NodeLocalized

theorem solution (N : ℕ) [NeZero N] {L : Type*} [CommRing L] (A : Subring L) :
    CharPReduction.modularRing N A = (NodeLocalized.modularEval N A).range := by
  apply le_antisymm
  · rw [CharPReduction.modularRing, Subring.closure_le]
    rintro x (⟨c, rfl⟩ | rfl | rfl)
    · exact ⟨MvPolynomial.C c, by simp [NodeLocalized.modularEval]⟩
    · exact ⟨MvPolynomial.X 0, by simp [NodeLocalized.modularEval]⟩
    · exact ⟨MvPolynomial.X 1, by simp [NodeLocalized.modularEval]⟩
  · rintro x ⟨p, rfl⟩
    induction p using MvPolynomial.induction_on with
    | C c =>
      rw [NodeLocalized.modularEval, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_C]
      exact CharPReduction.constSeries_mem_modularRing N A c
    | add p r hp hr => rw [map_add]; exact add_mem hp hr
    | mul_X p i hp =>
      rw [map_mul]
      refine mul_mem hp ?_
      rw [NodeLocalized.modularEval, MvPolynomial.eval₂Hom_X']
      fin_cases i
      · exact CharPReduction.jqModC_mem_modularRing N A
      · exact CharPReduction.jqNModC_mem_modularRing N A
end S_ModularCurve_modularRing_eq_range_modularEval
end P2MW

public section
set_option autoImplicit false

open ModularCurve ModularCurve.NodeLocalized
theorem ModularCurve.modularRing_eq_range_modularEval (N : ℕ) [NeZero N] {L : Type*} [CommRing L] (A : Subring L) :
    CharPReduction.modularRing N A = (NodeLocalized.modularEval N A).range := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_modularRing_eq_range_modularEval.solution
end
