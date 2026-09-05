module

public import Definitions.Def_ModularCurve_LevelOneProlongationPair
public import P2M.Sol.S_ModularCurve_modularUnitSeries_mem_modularFunctionFieldFull
import P2M.Sol.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_coeffEmb_modularUnitSeries_mem_integersFst
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

namespace P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_residue_coeffEmb_modularUnitSeries_ne_zero

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open AlgebraicCurve ModularCurve IsLocalRing

theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {P : PlaceSpecialization A q 1 data hKr k red hα hβ} (R : P.LevelOneProlongationPair)
    (h : (⟨coeffEmb (AlgebraicClosure ℚ) (modularUnitSeries (1 * q)),
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularUnitSeries_mem_modularFunctionFieldFull (1 * q))⟩ :
      ↥(modularFunctionFieldBar (1 * q))) ∈ R.R₁.integers) :
    R.R₁.residue ⟨_, h⟩ ≠ 0 := by
  obtain ⟨h', y, hy, hres⟩ :=
    ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coeffEmb_modularUnitSeries_mem_integersFst R
  have hq : ((1 * q : ℕ) : ℤ) = (q : ℤ) := by rw [one_mul]

  have hcoeff : ∀ n : ℤ, ((y.coeff n : A) : AlgebraicClosure ℚ)
      = algebraMap ℚ (AlgebraicClosure ℚ) ((modularUnitSeries (1 * q)).coeff n) := fun n => by
    have := congrArg (fun z : LaurentSeries (AlgebraicClosure ℚ) => z.coeff n) hy
    simp only [coeffMap_coeff, coeffEmb_coeff] at this
    exact this
  have hc : (modularUnitSeries (1 * q)).coeff (1 - (q : ℤ)) = 1 := by
    have := coeff_modularUnitSeries_self (1 * q)
    rwa [hq] at this
  have hy1 : y.coeff (1 - (q : ℤ)) = 1 := by
    apply Subtype.ext
    rw [OneMemClass.coe_one, hcoeff, hc, map_one]
  have hy0 : ∀ k : ℤ, k < 1 - (q : ℤ) → y.coeff k = 0 := fun k hk => by
    apply Subtype.ext
    rw [ZeroMemClass.coe_zero, hcoeff, coeff_modularUnitSeries_of_lt (1 * q) (by rw [hq]; exact hk),
      map_zero]

  have hres' : ((R.R₁.residue ⟨_, h⟩ : modularFunctionFieldFullC (ResidueField A) 1) :
      LaurentSeries (ResidueField A)) = coeffMap (IsLocalRing.residue A) y := hres
  have hc1 : (coeffMap (IsLocalRing.residue A) y).coeff (1 - (q : ℤ)) = 1 := by
    rw [coeffMap_coeff, hy1, map_one]
  intro h0
  have : ((R.R₁.residue ⟨_, h⟩ : modularFunctionFieldFullC (ResidueField A) 1) :
      LaurentSeries (ResidueField A)) = 0 := by rw [h0]; rfl
  rw [hres'] at this
  have h2 := congrArg (fun z : LaurentSeries (ResidueField A) => z.coeff (1 - (q : ℤ))) this
  simp only [HahnSeries.coeff_zero] at h2
  rw [hc1] at h2
  exact one_ne_zero h2
end S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_residue_coeffEmb_modularUnitSeries_ne_zero
end P2MW

public section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

open AlgebraicCurve ModularCurve IsLocalRing
theorem ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue_coeffEmb_modularUnitSeries_ne_zero
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {P : PlaceSpecialization A q 1 data hKr k red hα hβ} (R : P.LevelOneProlongationPair)
    (h : (⟨coeffEmb (AlgebraicClosure ℚ) (modularUnitSeries (1 * q)),
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularUnitSeries_mem_modularFunctionFieldFull (1 * q))⟩ :
      ↥(modularFunctionFieldBar (1 * q))) ∈ R.R₁.integers) :
    R.R₁.residue ⟨_, h⟩ ≠ 0 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_residue_coeffEmb_modularUnitSeries_ne_zero.solution
end
