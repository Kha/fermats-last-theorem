import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_ModularCurve_DegeneracyTower
import P2M.Util
import P2M.Sol.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_mem_integers_towerInclBar_and_coe_residue_eq
attribute [-instance] ModularCurve.PhiGen.instNeZeroPhiGenCosetA
attribute [-simp] ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option autoImplicit false

open AlgebraicCurve IsLocalRing open ModularCurve hiding coe_atkinLehnerInvolutionFull_mul_eq_of_coe_eq
open ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.exists_mem_integers_towerInclBar_and_coe_residue_eq
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ} (R : ProlongationTuple P)
    (ℓ : ℕ) [NeZero ℓ] (hqNℓ : ¬ q ∣ N * ℓ)
    {dataᵣ : ModularPolynomialData q} {hKrᵣ : KroneckerCongruence q dataᵣ}
    {hαᵣ : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) (N * ℓ) q}
    {hβᵣ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) (N * ℓ) q}
    {Pᵣ : PlaceSpecialization A q (N * ℓ) dataᵣ hKrᵣ k red hαᵣ hβᵣ} (Rᵣ : ProlongationTuple Pᵣ)
    (f : ↥(modularFunctionFieldBar (N * q))) :
    (∀ h : f ∈ R.R₁.integers,
      ∃ h' : towerInclBar (AlgebraicClosure ℚ)
          (mul_dvd_mul_right (dvd_mul_right N ℓ) q : N * q ∣ N * ℓ * q) f ∈ Rᵣ.R₁.integers,
        ((Rᵣ.residue₁ ⟨_, h'⟩ : ↥(modularFunctionFieldC k (N * ℓ))) : LaurentSeries k)
          = ((R.residue₁ ⟨f, h⟩ : ↥(modularFunctionFieldC k N)) : LaurentSeries k)) ∧
    (∀ h : f ∈ R.R₂.integers,
      ∃ h' : towerInclBar (AlgebraicClosure ℚ)
          (mul_dvd_mul_right (dvd_mul_right N ℓ) q : N * q ∣ N * ℓ * q) f ∈ Rᵣ.R₂.integers,
        ((Rᵣ.residue₂ ⟨_, h'⟩ : ↥(modularFunctionFieldC k (N * ℓ))) : LaurentSeries k)
          = ((R.residue₂ ⟨f, h⟩ : ↥(modularFunctionFieldC k N)) : LaurentSeries k)) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_mem_integers_towerInclBar_and_coe_residue_eq.solution
