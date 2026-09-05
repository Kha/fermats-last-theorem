module

public import Definitions.Def_ModularCurve_SupersingularModuli
public import Definitions.Def_WeierstrassCurve_HasseInvariant
import P2M.Sol.S_WeierstrassCurve_forall_nsmul_eq_zero_iff_hasseInvariant_eq_zero
import P2M.Util
public import Mathlib.FieldTheory.IsAlgClosed.Basic
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

namespace P2MW.S_ModularCurve_ssJSet_eq_ssJSetHasse

set_option autoImplicit false

open ModularCurve

theorem solution (q : ℕ) [Fact q.Prime] (hq : q ≠ 2)
    (K : Type*) [Field K] [IsAlgClosed K] [CharP K q] [DecidableEq K] :
    ssJSet q K = ssJSetHasse q K := by
  ext j
  simp only [ModularCurve.ssJSet, ModularCurve.ssJSetHasse, Set.mem_setOf_eq]
  constructor
  · intro h W _ hj
    exact (W.forall_nsmul_eq_zero_iff_hasseInvariant_eq_zero q hq).mp (h W hj)
  · intro h W _ hj
    exact (W.forall_nsmul_eq_zero_iff_hasseInvariant_eq_zero q hq).mpr (h W hj)
end S_ModularCurve_ssJSet_eq_ssJSetHasse
end P2MW

public section
open ModularCurve
theorem ModularCurve.ssJSet_eq_ssJSetHasse (q : ℕ) [Fact q.Prime] (hq : q ≠ 2)
    (K : Type*) [Field K] [IsAlgClosed K] [CharP K q] [DecidableEq K] :
    ssJSet q K = ssJSetHasse q K := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_ssJSet_eq_ssJSetHasse.solution
end
