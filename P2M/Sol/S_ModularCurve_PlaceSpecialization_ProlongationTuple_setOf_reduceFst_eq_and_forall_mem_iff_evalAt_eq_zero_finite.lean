import Mathlib
import Definitions.Def_ModularCurve_NodeDepth
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldBar
import P2M.Sol.S_AlgebraicCurve_Place_isRational_iff_deg_eq_one
import Theorems.Thm_ModularCurve_hasPrincipalDivisors_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_modularPolynomialFamily
import P2M.Sol.S_AlgebraicCurve_Place_evalAt_ne_zero
import P2M.Util
namespace P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_setOf_reduceFst_eq_and_forall_mem_iff_evalAt_eq_zero_finite
attribute [-instance] AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
attribute [-simp] AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 800000

open AlgebraicCurve ModularCurve ModularCurve.PlaceSpecialization

theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ}
    (R : ProlongationTuple P) (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (w : Place k (modularFunctionFieldC k N))
    (𝔮 : Ideal ↥(R.nodeIntegersOver K w)) (h𝔮0 : 𝔮 ≠ ⊥) :
    Set.Finite {V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) | (P.reduceFst V = w ∧
      ∀ g' : ↥(R.nodeIntegersOver K w), g' ∈ 𝔮 ↔ V.evalAt ((g' : ↥(modularFunctionFieldBar (N * q)))) = 0)} := by
  classical

  obtain ⟨f, hf𝔮, hf0⟩ : ∃ f ∈ 𝔮, f ≠ 0 := by
    by_contra h
    push Not at h
    exact h𝔮0 ((Submodule.eq_bot_iff 𝔮).mpr h)
  have hfF : ((f : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (N * q))) ≠ 0 :=
    fun h => hf0 (Subtype.ext h)

  haveI := ModularCurve.hasPrincipalDivisors_modularFunctionFieldBar ModularCurve.modularPolynomialFamily (N * q)
  obtain ⟨D, hD, -⟩ := AlgebraicCurve.HasPrincipalDivisors.exists_divisor (K := AlgebraicClosure ℚ)
    ((f : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (N * q))) hfF
  refine (D.support.finite_toSet).subset ?_
  rintro V ⟨-, hker⟩

  have hev : V.evalAt ((f : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (N * q))) = 0 := (hker f).mp hf𝔮
  have hrat : V.IsRational := by
    haveI := ModularCurve.isCurveOver_modularFunctionFieldBar (N * q)
    exact (AlgebraicCurve.Place.isRational_iff_deg_eq_one V).2 (AlgebraicCurve.IsCurveOver.deg_eq_one_of_isAlgClosed V)
  rw [Finset.mem_coe, Finsupp.mem_support_iff, hD V]
  intro hord
  exact (V.evalAt_ne_zero hrat hfF hord) hev
