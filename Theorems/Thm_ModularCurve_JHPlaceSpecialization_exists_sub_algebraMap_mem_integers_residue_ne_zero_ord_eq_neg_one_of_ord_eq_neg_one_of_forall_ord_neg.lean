import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Definitions.Def_AlgebraicCurve_AdelicIndex
import P2M.Util
import P2M.Sol.S_ModularCurve_JHPlaceSpecialization_exists_sub_algebraMap_mem_integers_residue_ne_zero_ord_eq_neg_one_of_ord_eq_neg_one_of_forall_ord_neg
attribute [-instance] AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions
attribute [-simp] AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none
set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve
open scoped MatrixGroups Classical

theorem ModularCurve.JHPlaceSpecialization.exists_sub_algebraMap_mem_integers_residue_ne_zero_ord_eq_neg_one_of_ord_eq_neg_one_of_forall_ord_neg
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    [NeZero (M / p)]
    (A : ValuationSubring (AlgebraicClosure ℚ))
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]

    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (α β : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα : α.IsIntegral) (hβ : β.IsIntegral)

    (δ : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) → Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))

    (Psp : JHPlaceSpecialization p M H hpM A) (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ)

    (S : Finset (ResidueField ↥A))
    (xj : ↥(xHFunctionFieldBar M H))

    (B : Finset (Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))
    (V₀ : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))
    (hB₁ : Psp.reduceFst α hα V₀ ∈ B) (hB₂ : Psp.reduceSnd β hβ δ V₀ ∈ B)
    (g : ↥(xHFunctionFieldBar M H)) (h₁ : g ∈ Rpd.R₁.integers) (h₂ : g ∈ Rpd.R₂.integers)
    (hgord : V₀.ord g = -1)
    (hfused : ∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), V ≠ V₀ → V.ord g < 0 →
      (∃ a : ↥A, 0 < V.ord (xj - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (a : (AlgebraicClosure ℚ))) ∧ IsLocalRing.residue ↥A a ∉ S) ∧
        Psp.reduceFst α hα V ∉ B ∧ Psp.reduceSnd β hβ δ V ∉ B) :
    ∃ (c : ↥A)
      (h₁' : g - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (c : (AlgebraicClosure ℚ)) ∈ Rpd.R₁.integers)
      (h₂' : g - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (c : (AlgebraicClosure ℚ)) ∈ Rpd.R₂.integers),
      (Rpd.R₁.residue ⟨g - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (c : (AlgebraicClosure ℚ)), h₁'⟩
        = Rpd.R₁.residue ⟨g, h₁⟩ - algebraMap (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) (IsLocalRing.residue ↥A c)) ∧
      (Rpd.R₂.residue ⟨g - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (c : (AlgebraicClosure ℚ)), h₂'⟩
        = Rpd.R₂.residue ⟨g, h₂⟩ - algebraMap (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) (IsLocalRing.residue ↥A c)) ∧
      (Rpd.R₁.residue ⟨g - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (c : (AlgebraicClosure ℚ)), h₁'⟩ ≠ 0) ∧
      (Rpd.R₂.residue ⟨g - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (c : (AlgebraicClosure ℚ)), h₂'⟩ ≠ 0) ∧
      (g - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (c : (AlgebraicClosure ℚ)) ≠ 0) ∧
      (V₀.ord (g - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (c : (AlgebraicClosure ℚ))) = -1) ∧
      (∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), V.ord (g - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (c : (AlgebraicClosure ℚ))) < 0 → V.ord g < 0) ∧
      (∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), V.ord g < 0 → V = V₀ ∨
        ∃ a : ↥A, 0 < V.ord (xj - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (a : (AlgebraicClosure ℚ))) ∧ IsLocalRing.residue ↥A a ∉ S) ∧
      Psp.reduceFst α hα V₀ ∈ B ∧ Psp.reduceSnd β hβ δ V₀ ∈ B ∧
      (∀ t', t' ∈ B → ∀ V'' : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), V'' ≠ V₀ → Psp.reduceFst α hα V'' = t' → 0 ≤ V''.ord (g - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (c : (AlgebraicClosure ℚ)))) ∧
      (∀ t', t' ∈ B → ∀ V'' : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), V'' ≠ V₀ → Psp.reduceSnd β hβ δ V'' = t' → 0 ≤ V''.ord (g - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (c : (AlgebraicClosure ℚ)))) ∧
      (∀ t', t' ∈ B → 0 < t'.ord (Rpd.R₁.residue ⟨g, h₁⟩ - algebraMap (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) (IsLocalRing.residue ↥A c)) → False) ∧
      (∀ t', t' ∈ B → 0 < t'.ord (Rpd.R₂.residue ⟨g, h₂⟩ - algebraMap (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) (IsLocalRing.residue ↥A c)) → False) ∧
      ∃ q : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H),
        (∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), q V = V.ord (g - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (c : (AlgebraicClosure ℚ)))) ∧ Divisor.degree q = 0 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_JHPlaceSpecialization_exists_sub_algebraMap_mem_integers_residue_ne_zero_ord_eq_neg_one_of_ord_eq_neg_one_of_forall_ord_neg.solution
