module

public import Definitions.Def_WeierstrassCurve_HasseInvariant
import P2M.Sol.S_WeierstrassCurve_hasseInvariant_variableChange
import P2M.Util
public import Mathlib.FieldTheory.IsSepClosed
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.EllipticCurve.IsomOfJ
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

namespace P2MW.S_WeierstrassCurve_hasseInvariant_pow_mul_delta_pow_eq_of_j_eq

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

open WeierstrassCurve

namespace P2mWs11W0

theorem hasseInvariant_pow_mul_Δ_pow_variableChange (q : ℕ) [Fact q.Prime]
    {R : Type*} [CommRing R] [CharP R q] (W : WeierstrassCurve R) (φ : VariableChange R) :
    hasseInvariant q (φ • W) ^ 12 * W.Δ ^ (q - 1) = hasseInvariant q W ^ 12 * (φ • W).Δ ^ (q - 1) := by
  rw [hasseInvariant_variableChange W φ, variableChange_Δ, mul_pow, mul_pow, ← pow_mul, ← pow_mul,
    mul_comm 12 (q - 1)]
  ring

end P2mWs11W0

open ModularCurve in
theorem solution
    (q : ℕ) [Fact q.Prime]
    {F : Type*} [Field F] [CharP F q] [IsSepClosed F]
    (W W' : WeierstrassCurve F) [W.IsElliptic] [W'.IsElliptic] (h : W.j = W'.j) :
    WeierstrassCurve.hasseInvariant q W ^ 12 * W'.Δ ^ (q - 1) =
      WeierstrassCurve.hasseInvariant q W' ^ 12 * W.Δ ^ (q - 1) := by
  obtain ⟨φ, rfl⟩ := WeierstrassCurve.exists_variableChange_of_j_eq W W' h
  exact (P2mWs11W0.hasseInvariant_pow_mul_Δ_pow_variableChange q W φ).symm
end S_WeierstrassCurve_hasseInvariant_pow_mul_delta_pow_eq_of_j_eq
end P2MW

public section
set_option synthInstance.maxHeartbeats 400000
set_option autoImplicit false

open ModularCurve

theorem WeierstrassCurve.hasseInvariant_pow_mul_delta_pow_eq_of_j_eq
    (q : ℕ) [Fact q.Prime]
    {F : Type*} [Field F] [CharP F q] [IsSepClosed F]
    (W W' : WeierstrassCurve F) [W.IsElliptic] [W'.IsElliptic] (h : W.j = W'.j) :
    WeierstrassCurve.hasseInvariant q W ^ 12 * W'.Δ ^ (q - 1) =
      WeierstrassCurve.hasseInvariant q W' ^ 12 * W.Δ ^ (q - 1) := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_hasseInvariant_pow_mul_delta_pow_eq_of_j_eq.solution
end
