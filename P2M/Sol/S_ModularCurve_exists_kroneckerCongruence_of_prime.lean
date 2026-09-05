module

import P2M.Sol.S_ModularCurve_kroneckerCongruence
import P2M.Sol.S_ModularCurve_nonempty_modularPolynomialData_of_squarefree
import P2M.Util
public import Definitions.Def_ModularCurve_KroneckerTransport
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

namespace P2MW.S_ModularCurve_exists_kroneckerCongruence_of_prime

theorem solution (ℓ : ℕ) [Fact ℓ.Prime] :
    ∃ data : ModularCurve.ModularPolynomialData ℓ, ModularCurve.KroneckerCongruence ℓ data := by
  obtain ⟨data⟩ := ModularCurve.nonempty_modularPolynomialData_of_squarefree ℓ
    (Fact.out : ℓ.Prime).squarefree (Fact.out : ℓ.Prime).one_lt
  exact ⟨data, ModularCurve.kroneckerCongruence ℓ data⟩
end S_ModularCurve_exists_kroneckerCongruence_of_prime
end P2MW

public section
theorem ModularCurve.exists_kroneckerCongruence_of_prime (ℓ : ℕ) [Fact ℓ.Prime] :
    ∃ data : ModularCurve.ModularPolynomialData ℓ, ModularCurve.KroneckerCongruence ℓ data := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_kroneckerCongruence_of_prime.solution
end
