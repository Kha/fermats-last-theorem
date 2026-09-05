module

public import Definitions.Def_ModularCurve_CharPReduction
public import Mathlib.Data.Int.ConditionallyCompleteOrder
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

set_option autoImplicit false

namespace ModularCurve
namespace NodeLocalized
noncomputable section

def coeffSubring (A : ValuationSubring (AlgebraicClosure ℚ)) (K : IntermediateField ℚ (AlgebraicClosure ℚ)) :
    Subring (AlgebraicClosure ℚ) :=
  A.toSubring ⊓ K.toSubalgebra.toSubring

def redRestrict {k : Type*} [Field k] {A : ValuationSubring (AlgebraicClosure ℚ)} (red : A →+* k)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) : coeffSubring A K →+* k :=
  red.comp (Subring.inclusion inf_le_left)

def fieldOver (N : ℕ) [NeZero N] (K : IntermediateField ℚ (AlgebraicClosure ℚ)) : Subfield (LaurentSeries (AlgebraicClosure ℚ)) :=
  Subfield.closure (Set.range (CharPReduction.constSeries K.toSubalgebra.toSubring)
    ∪ {jqModC (AlgebraicClosure ℚ), jqNModC (AlgebraicClosure ℚ) N})

def jRing (A : ValuationSubring (AlgebraicClosure ℚ)) (K : IntermediateField ℚ (AlgebraicClosure ℚ)) :
    Subring (LaurentSeries (AlgebraicClosure ℚ)) :=
  Subring.closure (Set.range (CharPReduction.constSeries (coeffSubring A K)) ∪ {jqModC (AlgebraicClosure ℚ)})

def jIntegralClosure (N : ℕ) [NeZero N] (A : ValuationSubring (AlgebraicClosure ℚ)) (K : IntermediateField ℚ (AlgebraicClosure ℚ)) :
    Subring (LaurentSeries (AlgebraicClosure ℚ)) where
  carrier := {x | x ∈ fieldOver N K ∧ IsIntegral (jRing A K) x}
  zero_mem' := ⟨zero_mem _, isIntegral_zero⟩
  one_mem' := ⟨one_mem _, isIntegral_one⟩
  add_mem' := fun hx hy => ⟨add_mem hx.1 hy.1, hx.2.add hy.2⟩
  neg_mem' := fun hx => ⟨neg_mem hx.1, hx.2.neg⟩
  mul_mem' := fun hx hy => ⟨mul_mem hx.1 hy.1, hx.2.mul hy.2⟩

end
end NodeLocalized
end ModularCurve
