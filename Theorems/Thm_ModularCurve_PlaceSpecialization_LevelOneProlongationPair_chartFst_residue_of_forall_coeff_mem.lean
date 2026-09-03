import Mathlib
import Definitions.Def_ModularCurve_LevelOneChartFst
import P2M.Util
import P2M.Sol.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_chartFst_residue_of_forall_coeff_mem

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization
  ModularCurve.PlaceSpecialization.LevelOneProlongationPair

theorem ModularCurve.PlaceSpecialization.LevelOneProlongationPair.chartFst_residue_of_forall_coeff_mem
    {p : ℕ} [Fact p.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    [CharP (ResidueField ↥A) p] [DecidableEq (ResidueField ↥A)]
    {data : ModularPolynomialData p} {hKr : KroneckerCongruence p data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 p}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 p}
    {P : PlaceSpecialization A p 1 data hKr (ResidueField ↥A) (IsLocalRing.residue ↥A) hα hβ}
    (R : P.LevelOneProlongationPair)
    (S₁ : Set (Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p))))
    (Wn : Finset (Place (ResidueField ↥A) ↥(modularFunctionFieldC (ResidueField ↥A) 1)))
    (hWn : ∀ w, w ∈ Wn ↔ w ∈ ssPlaces p 1 (ResidueField ↥A)) (Γ : R.ChartFstSupply S₁)
    (f : ↥(modularFunctionFieldBar (1 * p)))
    (hf : ∀ n : ℤ, (f : LaurentSeries (AlgebraicClosure ℚ)).coeff n ∈ A) :
    ∃ h : f ∈ (chartFst R S₁ Wn hWn Γ).integers, ∀ n : ℤ,
      (((chartFst R S₁ Wn hWn Γ).residue ⟨f, h⟩ : ↥(modularFunctionFieldC (ResidueField ↥A) 1)) :
          LaurentSeries (ResidueField ↥A)).coeff n =
        IsLocalRing.residue ↥A ⟨(f : LaurentSeries (AlgebraicClosure ℚ)).coeff n, hf n⟩ := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_chartFst_residue_of_forall_coeff_mem.solution
