module

public import Definitions.Def_ModularCurve_HeckeOperator
public import Definitions.Def_ModularCurve_CuspidalClass
import P2M.Sol.S_ModularCurve_geomAut_atkinLehner_comp_legs
import P2M.Sol.S_ModularCurve_exists_isFrickeAutFull_of_neZero
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

namespace P2MW.S_ModularCurve_frickeInvolutionBar_comp_heckeAlphaBar_one

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open AlgebraicCurve ModularCurve

namespace Ws14Fricke

theorem isAtkinLehnerAutFull_one_of_isFrickeAutFull (q : ℕ) [NeZero q]
    {σ : modularFunctionFieldFull (1 * q) ≃ₐ[ℚ] modularFunctionFieldFull (1 * q)}
    (hσ : IsFrickeAutFull (1 * q) σ) : IsAtkinLehnerAutFull 1 q σ := by
  intro d _ hd
  obtain rfl : d = 1 := Nat.dvd_one.mp hd
  exact ⟨hσ 1 (1 * q) (one_mul _) inferInstance inferInstance,
    hσ (1 * q) 1 (mul_one _) inferInstance inferInstance⟩

theorem isAtkinLehnerAutFull_one_frickeInvolutionFull (q : ℕ) [NeZero q] :
    IsAtkinLehnerAutFull 1 q (frickeInvolutionFull (1 * q)) :=
  isAtkinLehnerAutFull_one_of_isFrickeAutFull q
    (isFrickeAutFull_frickeInvolutionFull (1 * q) (exists_isFrickeAutFull_of_neZero (1 * q)))
end Ws14Fricke

theorem solution (q : ℕ) [NeZero q] :
    (frickeInvolutionBar (1 * q)).toAlgHom.comp (heckeAlphaBar (AlgebraicClosure ℚ) 1 q)
      = heckeBetaBar (AlgebraicClosure ℚ) 1 q :=
  (geomAut_atkinLehner_comp_legs (AlgebraicClosure ℚ) 1 q (frickeInvolutionFull (1 * q))
    (Ws14Fricke.isAtkinLehnerAutFull_one_frickeInvolutionFull q)).1
end S_ModularCurve_frickeInvolutionBar_comp_heckeAlphaBar_one
end P2MW

public section
set_option autoImplicit false

open AlgebraicCurve ModularCurve
theorem ModularCurve.frickeInvolutionBar_comp_heckeAlphaBar_one (q : ℕ) [NeZero q] :
    (frickeInvolutionBar (1 * q)).toAlgHom.comp (heckeAlphaBar (AlgebraicClosure ℚ) 1 q)
      = heckeBetaBar (AlgebraicClosure ℚ) 1 q := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_frickeInvolutionBar_comp_heckeAlphaBar_one.solution
end
