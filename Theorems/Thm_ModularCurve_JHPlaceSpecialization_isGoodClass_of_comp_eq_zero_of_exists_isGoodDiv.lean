import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Definitions.Def_ModularCurve_ComponentGroup
import P2M.Util
import P2M.Sol.S_ModularCurve_JHPlaceSpecialization_isGoodClass_of_comp_eq_zero_of_exists_isGoodDiv
attribute [-instance] AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions
attribute [-simp] WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.JHNeronObjectAtP
open scoped MatrixGroups

theorem ModularCurve.JHPlaceSpecialization.isGoodClass_of_comp_eq_zero_of_exists_isGoodDiv
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) [NeZero (M / p)]
    (A : ValuationSubring (AlgebraicClosure ℚ))
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (α : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα : α.IsIntegral) (hβ : (θ.toAlgHom.comp α).IsIntegral)
    (δ : Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) → Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)))
    (SS : Finset (Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))))
    (hfix : ∀ s ∈ SS, JHPlaceSpecialization.Fixed p M H hpM A δ s.1 ∧ JHPlaceSpecialization.Fixed p M H hpM A δ s.2)
    (hSS0 : SS.Nonempty)
    (Psp : JHPlaceSpecialization p M H hpM A)
    (e : ↥SS → ℕ) (hpos : ∀ s, 0 < e s)
    (comp : ↥(JHPlaceSpecialization.inertiaInvariants M H A) →+ componentGroup e)
    (hlaw : ∀ (D : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H))))
        (hI : Pic0.mk D ∈ JHPlaceSpecialization.inertiaInvariants M H A),
        Psp.IsGoodDiv α (θ.toAlgHom.comp α) hα hβ δ (D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) →
        ∀ s₀ : ↥SS,
          comp ⟨Pic0.mk D, hI⟩ =
            (Psp.sndDiv α (θ.toAlgHom.comp α) hα hβ δ (D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))).degree •
              componentGroupProj e ((e s₀ : ℤ) • (LinearMap.proj s₀ : (↥SS → ℤ) →ₗ[ℤ] ℤ).comp (characterLattice ↥SS).subtype))
    (hG : ∃ G : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H),
        Divisor.IsPrincipal G ∧ Psp.IsGoodDiv α (θ.toAlgHom.comp α) hα hβ δ G ∧
          (Psp.fstDiv α (θ.toAlgHom.comp α) hα hβ δ G).degree = ((∑ s : ↥SS, Finset.univ.lcm e / e s : ℕ) : ℤ) ∧
          (Psp.sndDiv α (θ.toAlgHom.comp α) hα hβ δ G).degree = -((∑ s : ↥SS, Finset.univ.lcm e / e s : ℕ) : ℤ))
    (x : ↥(JHPlaceSpecialization.inertiaInvariants M H A))
    (hrep : ∃ D : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H))),
        Psp.IsGoodDiv α (θ.toAlgHom.comp α) hα hβ δ (D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) ∧ Pic0.mk D = (x : JH M H))
    (hx : comp x = 0) :
    Psp.IsGoodClass α (θ.toAlgHom.comp α) hα hβ δ SS (x : JH M H) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_JHPlaceSpecialization_isGoodClass_of_comp_eq_zero_of_exists_isGoodDiv.solution
