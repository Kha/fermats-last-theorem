module

public import P2M.Sol.S_ModularCurve_modularUnitSeries_mem_modularFunctionFieldFull
import P2M.Sol.S_AlgebraicCurve_Divisor_degree_eq_finrank_adjoin_of_eq_max_neg_ord
import P2M.Sol.S_ModularCurve_smul_cuspidalDivisor_apply_eq_ord
import P2M.Sol.S_ModularCurve_ord_cuspInftyBar_coeffEmb_modularUnitSeries
import P2M.Sol.S_ModularCurve_ord_cuspZeroBar_coeffEmb_modularUnitSeries
import P2M.Sol.S_ModularCurve_deg_cuspInftyBar
import P2M.Sol.S_ModularCurve_isCurveOver_modularFunctionFieldBar
import P2M.Sol.S_AlgebraicCurve_RationalFunctionField_finiteDimensional_lSpace_zero_of_constantsAreBase
import P2M.Sol.S_ModularCurve_constantsAreBase_modularFunctionFieldBar
import P2M.Sol.S_AlgebraicCurve_finiteDimensional_adjoin_of_transcendental
import P2M.Sol.S_ModularCurve_exists_transcendental_finiteDimensional_modularFunctionFieldBar
import P2M.Sol.S_AlgebraicCurve_Place_transcendental_of_ord_ne_zero
import P2M.Util
public import Definitions.Def_ModularCurve_CuspidalClass
import Definitions.Def_AlgebraicCurve_RatFuncPlaceInfty
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

namespace P2MW.S_ModularCurve_finrank_adjoin_coeffEmb_modularUnitSeries_inv

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open AlgebraicCurve ModularCurve IsLocalRing

theorem solution {q : ℕ} [Fact q.Prime] :
    Module.finrank (IntermediateField.adjoin (AlgebraicClosure ℚ)
        ({((⟨coeffEmb (AlgebraicClosure ℚ) (modularUnitSeries (1 * q)),
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularUnitSeries_mem_modularFunctionFieldFull (1 * q))⟩ :
      ↥(modularFunctionFieldBar (1 * q))))⁻¹} : Set ↥(modularFunctionFieldBar (1 * q))))
      ↥(modularFunctionFieldBar (1 * q)) = q - 1 := by
  haveI hq1 : Fact (1 * q).Prime := ⟨by rw [one_mul]; exact Fact.out⟩
  have hmem := modularUnitSeries_mem_modularFunctionFieldFull (1 * q)
  set u : ↥(modularFunctionFieldBar (1 * q)) := ⟨coeffEmb (AlgebraicClosure ℚ) (modularUnitSeries (1 * q)),
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hmem⟩ with hu_def
  have hq' : ((1 * q : ℕ) : ℤ) = (q : ℤ) := by rw [one_mul]
  have hq2 : (2 : ℤ) ≤ q := by exact_mod_cast (Fact.out : q.Prime).two_le

  have hinf : (cuspInftyBar (1 * q)).ord u = 1 - (q : ℤ) := by
    rw [hu_def, ord_cuspInftyBar_coeffEmb_modularUnitSeries (1 * q) hmem, hq']
  have hzero : (cuspZeroBar (1 * q)).ord u = (q : ℤ) - 1 := by
    rw [hu_def, ord_cuspZeroBar_coeffEmb_modularUnitSeries (1 * q) hmem, hq']
  have hne : cuspZeroBar (1 * q) ≠ cuspInftyBar (1 * q) := fun h => by
    rw [h, hinf] at hzero
    omega

  have htr : Transcendental (AlgebraicClosure ℚ) u :=
    Place.transcendental_of_ord_ne_zero (cuspInftyBar (1 * q)) (by rw [hinf]; omega)
  obtain ⟨x0, hx0, hfd0⟩ := exists_transcendental_finiteDimensional_modularFunctionFieldBar (1 * q)
  haveI := hfd0
  haveI hfd : FiniteDimensional (IntermediateField.adjoin (AlgebraicClosure ℚ) ({u} : Set _))
      ↥(modularFunctionFieldBar (1 * q)) := finiteDimensional_adjoin_of_transcendental x0 htr
  haveI : IsCurveOver (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) :=
    isCurveOver_modularFunctionFieldBar (1 * q)
  haveI : FiniteDimensional (AlgebraicClosure ℚ)
      ↥(LSpace (0 : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)))) :=
    RationalFunctionField.finiteDimensional_lSpace_zero_of_constantsAreBase (AlgebraicClosure ℚ) _
      (constantsAreBase_modularFunctionFieldBar (1 * q))

  set D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) :=
    ((q : ℤ) - 1) • Finsupp.single (cuspInftyBar (1 * q)) 1 with hD
  have hord : ∀ v : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)),
      v.ord u = (((q : ℤ) - 1) • cuspidalDivisor (1 * q)) v := fun v => by
    rw [← hq', hu_def, ← smul_cuspidalDivisor_apply_eq_ord (1 * q) hmem v]
  have hDv : ∀ v : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)), D v = max 0 (-v.ord u) := by
    classical
    intro v
    rw [hord v, cuspidalDivisor_def, hD]
    simp only [Finsupp.smul_apply, Finsupp.coe_sub, Pi.sub_apply, smul_eq_mul, Finsupp.single_apply]
    by_cases h1 : cuspInftyBar (1 * q) = v
    · have h2 : ¬ cuspZeroBar (1 * q) = v := fun h => hne (h.trans h1.symm)
      rw [if_pos h1, if_neg h2]
      have e : -(((q : ℤ) - 1) * (0 - 1)) = (q : ℤ) - 1 := by ring
      rw [e, max_eq_right (by omega), mul_one]
    · rw [if_neg h1, mul_zero]
      by_cases h2 : cuspZeroBar (1 * q) = v
      · rw [if_pos h2]
        have e : -(((q : ℤ) - 1) * (1 - 0)) = 1 - (q : ℤ) := by ring
        rw [e, max_eq_left (by omega)]
      · rw [if_neg h2]
        simp
  have hdeg := Divisor.degree_eq_finrank_adjoin_of_eq_max_neg_ord u htr D hDv
  have hdegD : Divisor.degree D = (q : ℤ) - 1 := by
    rw [hD, map_zsmul, Divisor.degree_single, deg_cuspInftyBar]
    simp

  have hadj : IntermediateField.adjoin (AlgebraicClosure ℚ) ({u⁻¹} : Set ↥(modularFunctionFieldBar (1 * q)))
      = IntermediateField.adjoin (AlgebraicClosure ℚ) ({u} : Set _) := by
    apply le_antisymm
    · exact IntermediateField.adjoin_simple_le_iff.mpr
        (inv_mem (IntermediateField.mem_adjoin_simple_self _ u))
    · refine IntermediateField.adjoin_simple_le_iff.mpr ?_
      have := inv_mem (IntermediateField.mem_adjoin_simple_self (AlgebraicClosure ℚ) u⁻¹)
      rwa [inv_inv] at this
  rw [hadj]
  have hfin : (Module.finrank (IntermediateField.adjoin (AlgebraicClosure ℚ) ({u} : Set _))
      ↥(modularFunctionFieldBar (1 * q)) : ℤ) = (q : ℤ) - 1 := by rw [← hdeg, hdegD]
  omega
end S_ModularCurve_finrank_adjoin_coeffEmb_modularUnitSeries_inv
end P2MW

public section
attribute [-simp] AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq
attribute [-simp] AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

open AlgebraicCurve ModularCurve IsLocalRing
theorem ModularCurve.finrank_adjoin_coeffEmb_modularUnitSeries_inv {q : ℕ} [Fact q.Prime] :
    Module.finrank (IntermediateField.adjoin (AlgebraicClosure ℚ)
        ({((⟨coeffEmb (AlgebraicClosure ℚ) (modularUnitSeries (1 * q)),
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularUnitSeries_mem_modularFunctionFieldFull (1 * q))⟩ :
      ↥(modularFunctionFieldBar (1 * q))))⁻¹} : Set ↥(modularFunctionFieldBar (1 * q))))
      ↥(modularFunctionFieldBar (1 * q)) = q - 1 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_finrank_adjoin_coeffEmb_modularUnitSeries_inv.solution
end
