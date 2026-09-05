module

public import Definitions.Def_AlgebraicCurve_DivisorPushPull
public import Definitions.Def_AlgebraicCurve_AdelicIndex
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

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace AlgebraicCurve

structure PoleDivisorPackage (K F : Type*) [Field K] [Field F] [Algebra K F] where

  x : F

  B : Divisor K F

  hB_eff : 0 ≤ B

  hx_mem : x ∈ LSpace B

  n : ℕ

  hn_pos : 0 < n

  degB_eq : Divisor.degree B = n

  c : ℕ

  u : Fin n → F

  hu_mem : ∀ i, u i ∈ LSpace (c • B)

  lin_indep : LinearIndependent K (fun p : ℕ × Fin n => x ^ p.1 * u p.2)

def HasPoleDivisorPackage (K F : Type*) [Field K] [Field F] [Algebra K F] : Prop :=
  Nonempty (PoleDivisorPackage K F)

variable {K E F : Type*} [Field K] [Field E] [Field F]
  [Algebra K E] [Algebra K F] [Algebra E F] [IsScalarTower K E F]

structure TranscendenceTower (K E F : Type*) [Field K] [Field E] [Field F]
    [Algebra K E] [Algebra K F] [Algebra E F] [IsScalarTower K E F] where

  x : E

  hx_indep : LinearIndependent K (fun j : ℕ => x ^ j)

  v : Place K E

  hvdeg : v.deg = 1

  hxv : v.ord x = -1

  hxreg : ∀ u : Place K E, u ≠ v → 0 ≤ u.ord x

namespace TranscendenceTower

variable (T : TranscendenceTower K E F)

abbrev xF : F := algebraMap E F T.x

def poleDivisor [Algebra.IsSeparable E F] [HasPrincipalDivisors K F] : Divisor K F :=
  Divisor.pullback F (Finsupp.single T.v 1)

def RegularOutside (A : Type*) [CommRing A] [Algebra A E] (T : TranscendenceTower K E F) : Prop :=
  ∀ u : Place K E, u ≠ T.v → ∀ a : A, algebraMap A E a ∈ u.toValuationSubring

end TranscendenceTower

structure IntegralBasisInLSpace [Algebra.IsSeparable E F] [HasPrincipalDivisors K F]
    (T : TranscendenceTower K E F) where

  c : ℕ

  u : Fin (Module.finrank E F) → F

  hu_indep : LinearIndependent E u

  hu_mem : ∀ i, u i ∈ LSpace (c • T.poleDivisor)

variable (K E F) in

def HasIntegralBasisInLSpace [Algebra.IsSeparable E F] [HasPrincipalDivisors K F]
    (T : TranscendenceTower K E F) : Prop :=
  Nonempty (IntegralBasisInLSpace T)

variable (K E F) in

def HasIntegralBasisRegularOutside [Algebra.IsSeparable E F] (T : TranscendenceTower K E F) : Prop :=
  ∃ u : Fin (Module.finrank E F) → F, LinearIndependent E u ∧
    ∀ i, ∀ w : Place K F, w.restrict E ≠ T.v → 0 ≤ w.ord (u i)

variable (K E F) in

def HasRegularFractionSubring (T : TranscendenceTower K E F) : Prop :=
  ∃ (A : Subalgebra K E), IsFractionRing A E ∧
    ∀ u : Place K E, u ≠ T.v → ∀ a ∈ A, a ∈ u.toValuationSubring

end AlgebraicCurve

end
