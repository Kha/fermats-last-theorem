module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Definitions.Def_ModularCurve_SupersingularModuli
import P2M.Sol.S_WeierstrassCurve_j_pow_q_sq_eq_j_of_forall_q_zsmul_eq_zero
import P2M.Util
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.EllipticCurve.ModelsWithJ
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

namespace P2MW.S_ModularCurve_ssJSet_finite

set_option autoImplicit false

p2m_open "ModularCurve P2MW.S_ModularCurve_ssJSet_finite.ModularCurve"

namespace ModularCurve p2m_export "ModularCurve" "ssJSet mem_ssJSet_iff" end ModularCurve
p2m_open_scoped "ModularCurve" in
open Polynomial in

theorem ModularCurve.solution_aux_pow_q_sq {K : Type*} [Field K] [IsAlgClosed K] [DecidableEq K]
    (q : ℕ) [Fact q.Prime] [CharP K q] {a : K} (ha : a ∈ ModularCurve.ssJSet q K) : a ^ (q ^ 2) = a := by
  have h := WeierstrassCurve.j_pow_q_sq_eq_j_of_forall_q_zsmul_eq_zero q (WeierstrassCurve.ofJ a)
    (fun P hP => (ModularCurve.mem_ssJSet_iff.mp ha) (WeierstrassCurve.ofJ a) (WeierstrassCurve.ofJ_j a) P
      (by rwa [natCast_zsmul] at hP))
  rwa [WeierstrassCurve.ofJ_j] at h

p2m_open_scoped "ModularCurve" in
open Polynomial in

theorem ModularCurve.solution_main {K : Type*} [Field K] [IsAlgClosed K] [DecidableEq K]
    (q : ℕ) [Fact q.Prime] [CharP K q] : (ModularCurve.ssJSet q K).Finite := by
  have hq : 1 < q ^ 2 :=
    calc 1 < q := (Fact.out : q.Prime).one_lt
      _ ≤ q * q := Nat.le_mul_self q
      _ = q ^ 2 := (sq q).symm
  have hne : (X ^ (q ^ 2) - X : K[X]) ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero K hq
  refine ((X ^ (q ^ 2) - X : K[X]).roots.toFinset.finite_toSet).subset ?_
  intro a ha
  rw [Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_roots hne, IsRoot, eval_sub, eval_pow,
    eval_X, sub_eq_zero]
  exact ModularCurve.solution_aux_pow_q_sq q ha

theorem solution (q : ℕ) [Fact q.Prime]
    (K : Type*) [Field K] [IsAlgClosed K] [CharP K q] [DecidableEq K] :
    (ModularCurve.ssJSet q K).Finite := ModularCurve.solution_main q
end S_ModularCurve_ssJSet_finite
end P2MW

public section
open ModularCurve
namespace ModularCurve
theorem ssJSet_finite (q : ℕ) [Fact q.Prime]
    (K : Type*) [Field K] [IsAlgClosed K] [CharP K q] [DecidableEq K] :
    (ssJSet q K).Finite := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_ssJSet_finite.solution
end ModularCurve
end
