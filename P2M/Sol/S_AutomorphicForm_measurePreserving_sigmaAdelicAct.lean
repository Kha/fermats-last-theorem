import Definitions.Def_AutomorphicForm_SigmaAdelicAction
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_HaarMeasure_HaarChar_FiniteOrderAutomorphism
import P2M.Util
namespace P2MW.S_AutomorphicForm_measurePreserving_sigmaAdelicAct

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar

attribute [local instance] NumberField.AdelicHaar.glBorel

namespace SigmaActHaarSol

open AutomorphicForm

variable (F E : Type) [Field F] [Field E] [NumberField E] [Algebra F E]
variable (D : M4aHerbrand.IdeleGaloisDescent (𝓞 E) F E)

private noncomputable def cme (σ : E ≃ₐ[F] E) :
    Matrix.GeneralLinearGroup (Fin 2) (AdeleRing (𝓞 E) E) ≃ₜ*
      Matrix.GeneralLinearGroup (Fin 2) (AdeleRing (𝓞 E) E) :=
  { MonoidHom.toMulEquiv (sigmaAdelicAct F E D σ) (sigmaAdelicAct F E D σ⁻¹)
      (by rw [← sigmaAdelicAct_mul, inv_mul_cancel, sigmaAdelicAct_one])
      (by rw [← sigmaAdelicAct_mul, mul_inv_cancel, sigmaAdelicAct_one]) with
    continuous_toFun := continuous_sigmaAdelicAct F E D σ
    continuous_invFun := continuous_sigmaAdelicAct F E D σ⁻¹ }

private theorem coe_cme (σ : E ≃ₐ[F] E) : ⇑(cme F E D σ) = ⇑(sigmaAdelicAct F E D σ) := rfl

private theorem iterate_cme (σ : E ≃ₐ[F] E) (n : ℕ) :
    (⇑(cme F E D σ))^[n] = ⇑(sigmaAdelicAct F E D (σ ^ n)) := by
  induction n with
  | zero =>
    rw [Function.iterate_zero, pow_zero, sigmaAdelicAct_one]
    rfl
  | succ n ih =>
    rw [Function.iterate_succ', ih, pow_succ', sigmaAdelicAct_mul, coe_cme]
    rfl

private theorem finite_algEquiv : Finite (E ≃ₐ[F] E) := by
  haveI : CharZero F := RingHom.charZero (algebraMap F E)
  exact Finite.of_injective (fun σ : E ≃ₐ[F] E => σ.restrictScalars ℚ)
    (AlgEquiv.restrictScalars_injective ℚ)

end SigmaActHaarSol

open AutomorphicForm in
theorem solution (F E : Type) [Field F] [Field E]
    [NumberField E] [Algebra F E] (D : M4aHerbrand.IdeleGaloisDescent (𝓞 E) F E)
    (σ : E ≃ₐ[F] E) :
    MeasurePreserving (sigmaAdelicAct F E D σ) (adelicGLHaar (Fin 2) (𝓞 E) E)
      (adelicGLHaar (Fin 2) (𝓞 E) E) := by
  haveI := borelSpace_glBorel (Fin 2) (𝓞 E) E
  haveI := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 E) E
  haveI : (adelicGLHaar (Fin 2) (𝓞 E) E).Regular := Measure.regular_haarMeasure
  haveI := SigmaActHaarSol.finite_algEquiv F E
  exact MeasureTheory.measurePreserving_haar_of_iterate_eq_id (adelicGLHaar (Fin 2) (𝓞 E) E)
    (SigmaActHaarSol.cme F E D σ) (orderOf_pos σ).ne' (fun g => by
      rw [SigmaActHaarSol.iterate_cme, pow_orderOf_eq_one, sigmaAdelicAct_one]
      rfl)
