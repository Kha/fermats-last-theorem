module

public import Definitions.Def_ModularCurve_FibrePoly
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
import Mathlib.Topology.Sheaves.Init

namespace P2MW.S_ModularCurve_fibrePoly_eq_of_kroneckerCongruence
open Polynomial ModularCurve
theorem solution {k : Type*} [Field k]
    {ℓ : ℕ} [Fact ℓ.Prime] [CharP k ℓ] (data : ModularCurve.ModularPolynomialData ℓ)
    (hK : ModularCurve.KroneckerCongruence ℓ data) (a : k) :
    ModularCurve.fibrePoly data.Φ a =
      (Polynomial.C (a ^ ℓ) - Polynomial.X) * (Polynomial.C a - Polynomial.X ^ ℓ) := by
  have hK' : reduceModBivar ℓ data.Φ =
      (Polynomial.C Polynomial.X ^ ℓ - Polynomial.X) *
        (Polynomial.C Polynomial.X - Polynomial.X ^ ℓ) := hK
  rw [fibrePoly_eq_map_reduceModBivar (ℓ := ℓ), hK']
  simp only [Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X,
    Polynomial.map_C, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X, map_pow]
end S_ModularCurve_fibrePoly_eq_of_kroneckerCongruence
end P2MW

public section
open Polynomial
theorem ModularCurve.fibrePoly_eq_of_kroneckerCongruence {k : Type*} [Field k]
    {ℓ : ℕ} [Fact ℓ.Prime] [CharP k ℓ] (data : ModularCurve.ModularPolynomialData ℓ)
    (hK : ModularCurve.KroneckerCongruence ℓ data) (a : k) :
    ModularCurve.fibrePoly data.Φ a =
      (Polynomial.C (a ^ ℓ) - Polynomial.X) * (Polynomial.C a - Polynomial.X ^ ℓ) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_fibrePoly_eq_of_kroneckerCongruence.solution
end
