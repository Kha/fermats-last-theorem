module

public import Definitions.Def_ModularCurve_SpecializeModuli
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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

namespace P2MW.S_ModularCurve_algebraMap_residueField_charLGeomPlaceOfPoint_surjective

open AlgebraicCurve ModularCurve

theorem solution
    (K : Type*) [Field K] (a : K) :
    Function.Surjective (algebraMap K (ModularCurve.charLGeomPlaceOfPoint K a).ResidueField) := by

  have key : ∀ v : Place K (modularFunctionFieldC K 1), v.deg = 1 →
      Function.Surjective (algebraMap K v.ResidueField) := by
    intro v hv x
    haveI : Module.Free K v.ResidueField := Module.Free.of_divisionRing K v.ResidueField
    have hbt : (⊥ : Subalgebra K v.ResidueField) = ⊤ :=
      Subalgebra.bot_eq_top_iff_finrank_eq_one.mpr hv
    have hx : x ∈ (⊥ : Subalgebra K v.ResidueField) := hbt ▸ Algebra.mem_top
    exact Algebra.mem_bot.mp hx
  exact key _ (ModularCurve.deg_charLGeomPlaceOfPoint K a)
end S_ModularCurve_algebraMap_residueField_charLGeomPlaceOfPoint_surjective
end P2MW

public section
open AlgebraicCurve ModularCurve
theorem ModularCurve.algebraMap_residueField_charLGeomPlaceOfPoint_surjective
    (K : Type*) [Field K] (a : K) :
    Function.Surjective (algebraMap K (ModularCurve.charLGeomPlaceOfPoint K a).ResidueField) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_algebraMap_residueField_charLGeomPlaceOfPoint_surjective.solution
end
