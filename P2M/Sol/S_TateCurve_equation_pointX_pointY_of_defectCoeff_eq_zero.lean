module

public import Definitions.Def_TateCurve_Defect
import P2M.Sol.S_TateCurve_equation_of_defectCoeff_eq_zero
import P2M.Sol.S_TateCurve_exists_zpow_mul_mem_annulus
import P2M.Sol.S_TateCurve_pointX_zpow_mul
import P2M.Sol.S_TateCurve_pointY_zpow_mul
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

namespace P2MW.S_TateCurve_equation_pointX_pointY_of_defectCoeff_eq_zero
open TateCurve
open scoped NNReal

theorem solution {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
    [CompleteSpace K] {q u : K}
    (hD : ∀ v : K, v ≠ 0 → v ≠ 1 → ∀ N : ℕ, 0 < N → defectCoeff v N = 0)
    (hq0 : q ≠ 0) (hq : ‖q‖₊ < 1) (hu0 : u ≠ 0) (hu : ∀ n : ℤ, q ^ n * u ≠ 1) :
    pointY q u ^ 2 + pointX q u * pointY q u
      = pointX q u ^ 3 + a₄ q * pointX q u + a₆ q := by
  obtain ⟨n, hqu, hqu'⟩ := TateCurve.exists_zpow_mul_mem_annulus hq0 hq hu0
  have hv0 : q ^ n * u ≠ 0 := mul_ne_zero (zpow_ne_zero n hq0) hu0
  have hvlat : ∀ m : ℤ, q ^ m * (q ^ n * u) ≠ 1 := by
    intro m; rw [← mul_assoc, ← zpow_add₀ hq0]; exact hu (m + n)
  have hv1 : q ^ n * u ≠ 1 := by simpa using hvlat 0
  have heq := TateCurve.equation_of_defectCoeff_eq_zero hq0 hq hv0 hvlat hqu hqu' (hD _ hv0 hv1)
  rwa [TateCurve.pointX_zpow_mul hq0 n, TateCurve.pointY_zpow_mul hq0 n] at heq
end S_TateCurve_equation_pointX_pointY_of_defectCoeff_eq_zero
end P2MW

public section
open TateCurve
open scoped NNReal
theorem TateCurve.equation_pointX_pointY_of_defectCoeff_eq_zero {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {q u : K} (hD : ∀ v : K, v ≠ 0 → v ≠ 1 → ∀ N : ℕ, 0 < N → defectCoeff v N = 0) (hq0 : q ≠ 0) (hq : ‖q‖₊ < 1) (hu0 : u ≠ 0) (hu : ∀ n : ℤ, q ^ n * u ≠ 1) : pointY q u ^ 2 + pointX q u * pointY q u = pointX q u ^ 3 + a₄ q * pointX q u + a₆ q := by p2m_exact_reverting @_root_.P2MW.S_TateCurve_equation_pointX_pointY_of_defectCoeff_eq_zero.solution
end
