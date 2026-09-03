import Mathlib
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import P2M.Util
import P2M.Sol.S_ModularCurve_XHDRModelAtP_coeffMap_residue_mem_and_sub_algebraMap_mem_nonunits_pointEquivPlace_mfib_of_comp_efib_eq

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve
  IsLocalRing ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP
open scoped MatrixGroups

theorem ModularCurve.XHDRModelAtP.coeffMap_residue_mem_and_sub_algebraMap_mem_nonunits_pointEquivPlace_mfib_of_comp_efib_eq
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ)) :
    (∀ (y : {q : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ (𝔛.Mfib A hA ρ hρ).C // q ≫ (𝔛.Mfib A hA ρ hρ).toBase = 𝟙 _})
      (β : ↥(chartAlgFin p (ΓN p M H hpM) hj) →+* ResidueField ↥A),
      y.1 ≫ 𝔛.efib A hA ρ hρ ≫ pullback.fst (toBase p (ΓN p M H hpM) hj) _ =
        Spec.map (CommRingCat.ofHom β) ≫ ιFin p (ΓN p M H hpM) hj →
      ∀ (b : ↥(chartAlgFin p (ΓN p M H hpM) hj)) (yb : LaurentSeries ↥A),
        coeffMap A.subtype yb = coeffEmb (AlgebraicClosure ℚ) ((b : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))) : LaurentSeries ℚ) →
        ∃ hmem : coeffMap (IsLocalRing.residue ↥A) yb ∈ qExpFunctionFieldC (ResidueField ↥A) (ΓN p M H hpM),
          (⟨coeffMap (IsLocalRing.residue ↥A) yb, hmem⟩ : ↥(qExpFunctionFieldC (ResidueField ↥A) (ΓN p M H hpM))) ∈ ((𝔛.Mfib A hA ρ hρ).pointEquivPlace y).toValuationSubring ∧
          (⟨coeffMap (IsLocalRing.residue ↥A) yb, hmem⟩ : ↥(qExpFunctionFieldC (ResidueField ↥A) (ΓN p M H hpM))) -
              algebraMap (ResidueField ↥A) ↥(qExpFunctionFieldC (ResidueField ↥A) (ΓN p M H hpM)) (β b) ∈
            ((𝔛.Mfib A hA ρ hρ).pointEquivPlace y).toValuationSubring.nonunits) ∧
    (∀ (y : {q : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ (𝔛.Mfib A hA ρ hρ).C // q ≫ (𝔛.Mfib A hA ρ hρ).toBase = 𝟙 _})
      (β : ↥(chartAlgInf p (ΓN p M H hpM) hj) →+* ResidueField ↥A),
      y.1 ≫ 𝔛.efib A hA ρ hρ ≫ pullback.fst (toBase p (ΓN p M H hpM) hj) _ =
        Spec.map (CommRingCat.ofHom β) ≫ ιInf p (ΓN p M H hpM) hj →
      ∀ (b : ↥(chartAlgInf p (ΓN p M H hpM) hj)) (yb : LaurentSeries ↥A),
        coeffMap A.subtype yb = coeffEmb (AlgebraicClosure ℚ) ((b : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))) : LaurentSeries ℚ) →
        ∃ hmem : coeffMap (IsLocalRing.residue ↥A) yb ∈ qExpFunctionFieldC (ResidueField ↥A) (ΓN p M H hpM),
          (⟨coeffMap (IsLocalRing.residue ↥A) yb, hmem⟩ : ↥(qExpFunctionFieldC (ResidueField ↥A) (ΓN p M H hpM))) ∈ ((𝔛.Mfib A hA ρ hρ).pointEquivPlace y).toValuationSubring ∧
          (⟨coeffMap (IsLocalRing.residue ↥A) yb, hmem⟩ : ↥(qExpFunctionFieldC (ResidueField ↥A) (ΓN p M H hpM))) -
              algebraMap (ResidueField ↥A) ↥(qExpFunctionFieldC (ResidueField ↥A) (ΓN p M H hpM)) (β b) ∈
            ((𝔛.Mfib A hA ρ hρ).pointEquivPlace y).toValuationSubring.nonunits) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_XHDRModelAtP_coeffMap_residue_mem_and_sub_algebraMap_mem_nonunits_pointEquivPlace_mfib_of_comp_efib_eq.solution
