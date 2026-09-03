import Mathlib
import Definitions.Def_DrinfeldCurve_FunctionField
import Definitions.Def_DrinfeldCurve_LocalChart
import P2M.Util
import P2M.Sol.S_DrinfeldCurve_LocalChart_exists_algEquiv_coordRing_and_isDiscreteValuationRing_blowupChart_of_mem_maximalIdeal

set_option autoImplicit false

noncomputable section

open MvPowerSeries IsLocalRing DrinfeldCurve DrinfeldCurve.LocalChart

theorem DrinfeldCurve.LocalChart.exists_algEquiv_coordRing_and_isDiscreteValuationRing_blowupChart_of_mem_maximalIdeal
    (q : ℕ) [Fact q.Prime]
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra (GaloisField q 2) (ResidueField O)]
    [IsAlgClosed (ResidueField O)] [IsDomain (CoordRing q (ResidueField O))]
    (π : O) (hπ : maximalIdeal O = Ideal.span {π})
    (ϖ : O) (hϖ : ϖ ∈ maximalIdeal O) (hϖ0 : ϖ ≠ 0)
    (pr : ChartPresentation q O ϖ)
    (hnzd : Ideal.Quotient.mk (Ideal.span {pr.rel}) (C ϖ) ∈ nonZeroDivisors pr.Ring) :
    let S := pr.Ring
    let mkS : MvPowerSeries (Fin 2) O →+* S := Ideal.Quotient.mk _
    let L := Localization.Away (mkS (C ϖ))
    let ι₀ : O →+* L := (algebraMap S L).comp (mkS.comp (C (σ := Fin 2) (R := O)))
    let x₀ : L := algebraMap S L (mkS (X 0)) * IsLocalization.Away.invSelf (S := L) (mkS (C ϖ))
    let x₁ : L := algebraMap S L (mkS (X 1)) * IsLocalization.Away.invSelf (S := L) (mkS (C ϖ))
    let R : Subring L := Subring.closure (Set.range (algebraMap S L) ∪ {x₀, x₁})
    ∃ (hι₀ : ∀ o : O, ι₀ o ∈ R) (hx₀ : x₀ ∈ R) (hx₁ : x₁ ∈ R)
      (P : Ideal ↥R) (_ : P = Ideal.span {(⟨ι₀ π, hι₀ π⟩ : ↥R)})
      (_ : IsNoetherianRing ↥R) (hP : P.IsPrime)
      (algR : Algebra (ResidueField O) (↥R ⧸ P))
      (_ : ∀ a : O, algebraMap (ResidueField O) (↥R ⧸ P) (residue O a) = Ideal.Quotient.mk P ⟨ι₀ a, hι₀ a⟩)
      (eR : (↥R ⧸ P) ≃ₐ[ResidueField O] CoordRing q (ResidueField O))
      (c : ResidueField O),

      (∀ s : S, (∃ a ∈ maximalIdeal O, ∃ g₀ g₁ : MvPowerSeries (Fin 2) O, s = mkS (C a + X 0 * g₀ + X 1 * g₁)) →
        ∃ h : algebraMap S L s ∈ R, (⟨_, h⟩ : ↥R) ∈ P) ∧

      c ≠ 0 ∧
      c ^ (q + 1) * residue O (MvPowerSeries.constantCoeff pr.u) = residue O (MvPowerSeries.constantCoeff pr.v) ∧
      eR (Ideal.Quotient.mk P ⟨x₀, hx₀⟩) =
        algebraMap (ResidueField O) (CoordRing q (ResidueField O)) c * x q (ResidueField O) ∧
      eR (Ideal.Quotient.mk P ⟨x₁, hx₁⟩) =
        algebraMap (ResidueField O) (CoordRing q (ResidueField O)) c * y q (ResidueField O) ∧

      (letI := hP
       ∃ (_ : IsDomain (Localization.AtPrime P)),
       IsDiscreteValuationRing (Localization.AtPrime P) ∧
       maximalIdeal (Localization.AtPrime P) =
         Ideal.span {algebraMap (↥R) (Localization.AtPrime P) ⟨ι₀ π, hι₀ π⟩} ∧
       ∃ (algW : Algebra (ResidueField O) (ResidueField (Localization.AtPrime P)))
         (_ : ∀ a : O, algebraMap (ResidueField O) (ResidueField (Localization.AtPrime P)) (residue O a) =
           residue (Localization.AtPrime P) (algebraMap (↥R) _ ⟨ι₀ a, hι₀ a⟩))
         (eW : ResidueField (Localization.AtPrime P) ≃ₐ[ResidueField O] drinfeldFunctionField q (ResidueField O)),
         ∀ r : ↥R, eW (residue (Localization.AtPrime P) (algebraMap (↥R) _ r)) =
           algebraMap (CoordRing q (ResidueField O)) (drinfeldFunctionField q (ResidueField O)) (eR (Ideal.Quotient.mk P r))) := by p2m_exact_reverting @_root_.P2MW.S_DrinfeldCurve_LocalChart_exists_algEquiv_coordRing_and_isDiscreteValuationRing_blowupChart_of_mem_maximalIdeal.solution
