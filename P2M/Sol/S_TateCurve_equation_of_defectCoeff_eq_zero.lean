module

public import Definitions.Def_TateCurve_Defect
import P2M.Sol.S_TateCurve_defectCoeff_zero
import P2M.Sol.S_TateCurve_defect_qExpansion
import P2M.Util
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.ReduceModChar
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

namespace P2MW.S_TateCurve_equation_of_defectCoeff_eq_zero
open TateCurve
open scoped NNReal

theorem solution {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
    [CompleteSpace K] {q u : K} (hq0 : q ≠ 0) (hq : ‖q‖₊ < 1) (hu0 : u ≠ 0)
    (hu : ∀ n : ℤ, q ^ n * u ≠ 1) (hqu : ‖q * u‖₊ < 1) (hqu' : ‖q * u⁻¹‖₊ < 1)
    (h : ∀ N : ℕ, 0 < N → defectCoeff u N = 0) :
    pointY q u ^ 2 + pointX q u * pointY q u
      = pointX q u ^ 3 + a₄ q * pointX q u + a₆ q := by
  have hu1 : u ≠ 1 := by simpa using hu 0
  have hall : ∀ N : ℕ, defectCoeff u N = 0 := by
    intro N; cases N with
    | zero => exact TateCurve.defectCoeff_zero hu1
    | succ n => exact h (n + 1) n.succ_pos
  have hexp := TateCurve.defect_qExpansion hq0 hq hu0 hu hqu hqu'
  have hzero : ∑' N : ℕ, defectCoeff u N * q ^ N = 0 := by
    have hterm : ∀ N : ℕ, defectCoeff u N * q ^ N = 0 := fun N => by rw [hall N, zero_mul]
    rw [tsum_congr hterm, tsum_zero]
  rw [hzero] at hexp
  exact sub_eq_zero.mp hexp
end S_TateCurve_equation_of_defectCoeff_eq_zero
end P2MW

public section
open TateCurve
open scoped NNReal
theorem TateCurve.equation_of_defectCoeff_eq_zero {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {q u : K} (hq0 : q ≠ 0) (hq : ‖q‖₊ < 1) (hu0 : u ≠ 0) (hu : ∀ n : ℤ, q ^ n * u ≠ 1) (hqu : ‖q * u‖₊ < 1) (hqu' : ‖q * u⁻¹‖₊ < 1) (h : ∀ N : ℕ, 0 < N → defectCoeff u N = 0) : pointY q u ^ 2 + pointX q u * pointY q u = pointX q u ^ 3 + a₄ q * pointX q u + a₆ q := by p2m_exact_reverting @_root_.P2MW.S_TateCurve_equation_of_defectCoeff_eq_zero.solution
end
