module

public import Definitions.Def_AlgebraicCurve_PlaceEvaluation
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
import Mathlib.Order.CompletePartialOrder
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

namespace P2MW.S_AlgebraicCurve_Place_isRational_iff_deg_eq_one

open AlgebraicCurve

theorem solution {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) : v.IsRational ↔ v.deg = 1 := by
  constructor
  · intro hv
    have hbij : Function.Bijective (algebraMap K v.ResidueField) :=
      ⟨v.algebraMap_residueField_injective, hv⟩
    show Module.finrank K v.ResidueField = 1
    rw [← Module.finrank_self K]
    exact ((AlgEquiv.ofBijective (Algebra.ofId K v.ResidueField) hbij).toLinearEquiv.finrank_eq).symm
  · intro h x
    have hbot : (⊥ : Subalgebra K v.ResidueField) = ⊤ :=
      Subalgebra.bot_eq_top_iff_finrank_eq_one.mpr h
    have hx : x ∈ (⊥ : Subalgebra K v.ResidueField) := by
      rw [hbot]
      exact Algebra.mem_top
    exact Algebra.mem_bot.mp hx
end S_AlgebraicCurve_Place_isRational_iff_deg_eq_one
end P2MW

public section
open AlgebraicCurve
theorem AlgebraicCurve.Place.isRational_iff_deg_eq_one {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) : v.IsRational ↔ v.deg = 1 := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Place_isRational_iff_deg_eq_one.solution
end
