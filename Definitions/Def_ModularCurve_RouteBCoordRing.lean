module

public import Definitions.Def_ModularCurve_X0
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

@[expose] public section

noncomputable section

open IntermediateField

namespace ModularCurve

section Tower

variable (N : ℕ) [NeZero N]

def jAdjoinRingHom : ℚ⟮jq⟯ →+* modularFunctionField N where
  toFun x := ⟨(x : LaurentSeries ℚ), adjoin_jq_le N x.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

@[reducible] def algebraIntPolyModularFunctionField : Algebra (Polynomial ℤ) (modularFunctionField N) :=
  ((jAdjoinRingHom N).comp evalAtJGen).toAlgebra

attribute [local instance] algebraIntPolyModularFunctionField

abbrev routeBCoordRing : Subalgebra (Polynomial ℤ) (modularFunctionField N) :=
  integralClosure (Polynomial ℤ) (modularFunctionField N)

def routeBJValue {N : ℕ} [NeZero N] {L : Type*} [CommRing L] (φ : ↥(routeBCoordRing N) →+* L) : L :=
  φ ⟨algebraMap (Polynomial ℤ) ↥(modularFunctionField N) Polynomial.X, Subalgebra.algebraMap_mem _ _⟩

end Tower

end ModularCurve

end
