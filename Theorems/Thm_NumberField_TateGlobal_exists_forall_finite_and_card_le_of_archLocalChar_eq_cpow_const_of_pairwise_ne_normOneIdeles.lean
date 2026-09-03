import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import P2M.Util
import P2M.Sol.S_NumberField_TateGlobal_exists_forall_finite_and_card_le_of_archLocalChar_eq_cpow_const_of_pairwise_ne_normOneIdeles
attribute [-instance] instCountableOfNumberField_definitions
attribute [-simp] NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq NumberField.SIdele.fibre_inr NumberField.SIdele.toFinite_hom_apply NumberField.SIdele.fibre_inl NumberField.SIdele.toArch_hom_apply GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply NumberField.SUnits.coe_unitOfValuedEqOne NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl NumberField.SUnits.val_zsmul NumberField.SUnits.val_add AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_one AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_one

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain AutomorphicForm

theorem NumberField.TateGlobal.exists_forall_finite_and_card_le_of_archLocalChar_eq_cpow_const_of_pairwise_ne_normOneIdeles
    (K : Type) [Field K] [NumberField K] :
    ∃ N : ℕ, ∀ (ι : Type) (χ : ι → ((AdeleRing (𝓞 K) K)ˣ →* ℂˣ)) (σ₀ : ι → ℝ),
      (∀ i, Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((χ i z : ℂˣ) : ℂ)) →
      (∀ i, IsIdeleClassChar (𝓞 K) K (χ i)) →
      (∀ i (v : HeightOneSpectrum (𝓞 K)), NumberField.TateGlobal.IsUnramifiedCharAt (χ i) v) →
      (∀ i (v : InfinitePlace K) (x : (v.Completion)ˣ),
        ((NumberField.TateGlobal.archLocalChar (χ i) v x : ℂˣ) : ℂ) =
          (((NumberField.TateGlobal.ideleNorm K (NumberField.TateGlobal.archUnitHom v x)) : ℝ) : ℂ) ^
            (((σ₀ i : ℝ) : ℂ) * Complex.I)) →
      (∀ i j, i ≠ j → ∃ z ∈ NumberField.TateGlobal.normOneIdeles K, χ i z ≠ χ j z) →
      Finite ι ∧ Nat.card ι ≤ N := by p2m_exact_reverting @_root_.P2MW.S_NumberField_TateGlobal_exists_forall_finite_and_card_le_of_archLocalChar_eq_cpow_const_of_pairwise_ne_normOneIdeles.solution
