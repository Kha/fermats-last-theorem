module

public import Definitions.Def_ModularCurve_KroneckerTransport
import P2M.Util
import Mathlib.Algebra.AffineMonoid.Basic
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
import Mathlib.Topology.Sheaves.Init

namespace P2MW.S_ModularCurve_existsUnique_kroneckerRemainder

p2m_open "Polynomial ModularCurve P2MW.S_ModularCurve_existsUnique_kroneckerRemainder.ModularCurve"

namespace ModularCurve
p2m_export "ModularCurve" "reduceModBivar reduceModBivar_X reduceModBivar_C_X KroneckerCongruence ModularPolynomialData"
namespace K2R
p2m_open "ModularCurve"

theorem C_C_dvd_of_reduceModBivar_eq_zero (p : ℕ) (D : Polynomial (Polynomial ℤ))
    (hD : reduceModBivar p D = 0) : C (C (p : ℤ)) ∣ D := by
  rw [Polynomial.C_dvd_iff_dvd_coeff]
  intro i
  rw [Polynomial.C_dvd_iff_dvd_coeff]
  intro j
  have h := congrArg (fun Q : Polynomial (Polynomial (ZMod p)) => (Q.coeff i).coeff j) hD
  simp only [reduceModBivar, Polynomial.coe_mapRingHom, Polynomial.coeff_map,
    Polynomial.coeff_zero, eq_intCast] at h
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp h

theorem main (p : ℕ) [Fact p.Prime]
    (data : ModularPolynomialData p) (hK : KroneckerCongruence p data) :
    ∃! R : Polynomial (Polynomial ℤ),
      data.Φ = (C X ^ p - X) * (C X - X ^ p) + C (C (p : ℤ)) * R := by
  have hp0 : (C (C (p : ℤ)) : Polynomial (Polynomial ℤ)) ≠ 0 := by
    simp [(Fact.out : p.Prime).ne_zero]

  have hred : reduceModBivar p (data.Φ - (C X ^ p - X) * (C X - X ^ p)) = 0 := by
    rw [map_sub, hK]
    simp [map_mul, map_sub, map_pow, reduceModBivar_X, reduceModBivar_C_X]
  obtain ⟨R, hR⟩ := C_C_dvd_of_reduceModBivar_eq_zero p _ hred
  refine ⟨R, ?_, ?_⟩
  · show data.Φ = (C X ^ p - X) * (C X - X ^ p) + C (C (p : ℤ)) * R
    rw [← hR]; ring
  · intro R' hR'
    have h : C (C (p : ℤ)) * R' = C (C (p : ℤ)) * R := by
      rw [← hR, hR']; ring
    exact mul_left_cancel₀ hp0 h

end ModularCurve.K2R

theorem solution (p : ℕ) [Fact p.Prime]
    (data : ModularPolynomialData p) (hK : KroneckerCongruence p data) :
    ∃! R : Polynomial (Polynomial ℤ),
      data.Φ = (C X ^ p - X) * (C X - X ^ p) + C (C (p : ℤ)) * R :=
  ModularCurve.K2R.main p data hK
end S_ModularCurve_existsUnique_kroneckerRemainder
end P2MW

public section
open Polynomial ModularCurve
theorem ModularCurve.existsUnique_kroneckerRemainder (p : ℕ) [Fact p.Prime]
    (data : ModularPolynomialData p) (hK : KroneckerCongruence p data) :
    ∃! R : Polynomial (Polynomial ℤ),
      data.Φ = (C X ^ p - X) * (C X - X ^ p) + C (C (p : ℤ)) * R := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_existsUnique_kroneckerRemainder.solution
end
