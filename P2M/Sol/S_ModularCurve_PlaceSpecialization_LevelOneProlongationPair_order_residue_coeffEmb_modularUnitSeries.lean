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

namespace P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_order_residue_coeffEmb_modularUnitSeries

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
    ((R.R₁.residue ⟨_, h⟩ : modularFunctionFieldFullC (ResidueField A) 1) :
        LaurentSeries (ResidueField A)).order = 1 - (q : ℤ) := by
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
  rw [hres']
  have hne : coeffMap (IsLocalRing.residue A) y ≠ 0 := fun h0 => by
    have := congrArg (fun z : LaurentSeries (ResidueField A) => z.coeff (1 - (q : ℤ))) h0
    simp only [HahnSeries.coeff_zero] at this
    rw [hc1] at this
    exact one_ne_zero this
  refine le_antisymm (HahnSeries.order_le_of_coeff_ne_zero (by rw [hc1]; exact one_ne_zero)) ?_
  by_contra hlt
  rw [not_le] at hlt
  have hz : (coeffMap (IsLocalRing.residue A) y).coeff (coeffMap (IsLocalRing.residue A) y).order = 0 := by
    rw [coeffMap_coeff, hy0 _ hlt, map_zero]
  exact hne (HahnSeries.coeff_order_eq_zero.mp hz)
end S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_order_residue_coeffEmb_modularUnitSeries
end P2MW

public section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

open AlgebraicCurve ModularCurve IsLocalRing
theorem ModularCurve.PlaceSpecialization.LevelOneProlongationPair.order_residue_coeffEmb_modularUnitSeries
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {P : PlaceSpecialization A q 1 data hKr k red hα hβ} (R : P.LevelOneProlongationPair)
    (h : (⟨coeffEmb (AlgebraicClosure ℚ) (modularUnitSeries (1 * q)),
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularUnitSeries_mem_modularFunctionFieldFull (1 * q))⟩ :
      ↥(modularFunctionFieldBar (1 * q))) ∈ R.R₁.integers) :
    ((R.R₁.residue ⟨_, h⟩ : modularFunctionFieldFullC (ResidueField A) 1) :
        LaurentSeries (ResidueField A)).order = 1 - (q : ℤ) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_order_residue_coeffEmb_modularUnitSeries.solution
end
