module

public import Definitions.Def_ModularCurve_ModuliPoint
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

def ssJSet (p : ℕ) (K : Type*) [Field K] [DecidableEq K] : Set K :=
  {j | ∀ (W : WeierstrassCurve K) [W.IsElliptic], W.j = j →
    ∀ P : W.toAffine.Point, p • P = 0 → P = 0}

theorem mem_ssJSet_iff {p : ℕ} {K : Type*} [Field K] [DecidableEq K] {j : K} :
    j ∈ ssJSet p K ↔ ∀ (W : WeierstrassCurve K) [W.IsElliptic], W.j = j →
      ∀ P : W.toAffine.Point, p • P = 0 → P = 0 :=
  Iff.rfl

def ModuliPoint.IsSupersingular (p : ℕ) {N : ℕ} {K : Type*} [Field K] [DecidableEq K]
    (x : ModuliPoint N K) : Prop :=
  x.j ∈ ssJSet p K

def ssLocus (p N : ℕ) (K : Type*) [Field K] [DecidableEq K] : Set (ModuliPoint N K) :=
  {x | x.IsSupersingular p}

theorem mem_ssLocus_iff {p N : ℕ} {K : Type*} [Field K] [DecidableEq K]
    {x : ModuliPoint N K} :
    x ∈ ssLocus p N K ↔ x.j ∈ ssJSet p K :=
  Iff.rfl

theorem isSupersingular_mk_iff {p N : ℕ} {K : Type*} [Field K] [DecidableEq K]
    {P : Gamma0Pair N K} :
    ModuliPoint.IsSupersingular p (Quot.mk _ P : ModuliPoint N K) ↔
      P.toCurve.j ∈ ssJSet p K :=
  Iff.rfl

end ModularCurve
