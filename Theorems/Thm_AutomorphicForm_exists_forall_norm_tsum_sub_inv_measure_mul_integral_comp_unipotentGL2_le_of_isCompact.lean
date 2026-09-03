import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_NumberField_AdelicHaar
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_forall_norm_tsum_sub_inv_measure_mul_integral_comp_unipotentGL2_le_of_isCompact
attribute [-instance] instCountableOfNumberField_definitions
attribute [-simp] AutomorphicForm.whittakerCoefficient_zero AutomorphicForm.CarrierPins.mk.injEq AutomorphicForm.CarrierPins.mk.sizeOf_spec NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicBox

theorem AutomorphicForm.exists_forall_norm_tsum_sub_inv_measure_mul_integral_comp_unipotentGL2_le_of_isCompact
    (F : Type) [Field F] [NumberField F]
    (φ : Matrix.GeneralLinearGroup (Fin 2) (AdeleRing (𝓞 F) F) → ℂ)
    (hφ : AutomorphicForm.IsFactorizableTestFn F φ)
    (Q : Set (Matrix.GeneralLinearGroup (Fin 2) (AdeleRing (𝓞 F) F) ×
      Matrix.GeneralLinearGroup (Fin 2) (AdeleRing (𝓞 F) F))) (hQ : IsCompact Q) (N : ℕ) :
    ∃ C : ℝ, ∀ p ∈ Q, ∀ (a : (AdeleRing (𝓞 F) F)ˣ) (t : ℝ), 1 ≤ t → (a : AdeleRing (𝓞 F) F).2 = 1 →
      (∀ w : InfinitePlace F, ‖(a : AdeleRing (𝓞 F) F).1 w‖ = t) → ∀ e : AdeleRing (𝓞 F) F,
        ‖(∑' β : F, φ (p.1 * AutomorphicForm.unipotentGL2
              ((algebraMap F (AdeleRing (𝓞 F) F) β + e) * ↑a⁻¹) * p.2)) -
            ((adelicAddHaar (𝓞 F) F (adelicBox F)).toReal : ℂ)⁻¹ *
              ∫ u, φ (p.1 * AutomorphicForm.unipotentGL2 ((u + e) * ↑a⁻¹) * p.2) ∂(adelicAddHaar (𝓞 F) F)‖
          ≤ C * t⁻¹ ^ N := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_forall_norm_tsum_sub_inv_measure_mul_integral_comp_unipotentGL2_le_of_isCompact.solution
