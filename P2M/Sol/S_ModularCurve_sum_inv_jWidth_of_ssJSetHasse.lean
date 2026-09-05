module

public import Definitions.Def_WeierstrassCurve_HasseInvariant
public import Definitions.Def_ModularCurve_JWidth
import P2M.Sol.S_ModularCurve_sum_inv_jWidth_of_deuringPolynomial
import P2M.Sol.S_ModularCurve_ssJSetHasse_eq_image_legendreJ_toFinset
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

namespace P2MW.S_ModularCurve_sum_inv_jWidth_of_ssJSetHasse

set_option autoImplicit false

open Polynomial ModularCurve Finset

theorem solution (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (K : Type*) [Field K]
    [IsAlgClosed K] [CharP K q] [DecidableEq K] (S : Finset K)
    (hS : ∀ j, j ∈ S ↔ j ∈ ssJSetHasse q K) :
    ∑ j ∈ S, ((jWidth j : ℚ))⁻¹ = ((q : ℚ) - 1) / 12 := by
  have hq2 : q ≠ 2 := by omega
  have hSZ : S = ((Polynomial.deuringPolynomial q).map (Int.castRingHom K)).roots.toFinset.image
      legendreJ := by
    ext j
    rw [hS, ssJSetHasse_eq_image_legendreJ_toFinset q hq2 K, ← Finset.coe_image, Finset.mem_coe]
  rw [hSZ]
  exact sum_inv_jWidth_of_deuringPolynomial q hq K
end S_ModularCurve_sum_inv_jWidth_of_ssJSetHasse
end P2MW

public section
open Polynomial ModularCurve Finset
theorem ModularCurve.sum_inv_jWidth_of_ssJSetHasse (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (K : Type*) [Field K]
    [IsAlgClosed K] [CharP K q] [DecidableEq K] (S : Finset K)
    (hS : ∀ j, j ∈ S ↔ j ∈ ssJSetHasse q K) :
    ∑ j ∈ S, ((jWidth j : ℚ))⁻¹ = ((q : ℚ) - 1) / 12 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_sum_inv_jWidth_of_ssJSetHasse.solution
end
