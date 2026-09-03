import Mathlib
import Definitions.Def_ModularCurve_ArithmeticGalois
import P2M.Util
namespace P2MW.S_ModularCurve_arithmeticGalois_smul_eq_self_of_forall_coeff_eq

set_option autoImplicit false

open ModularCurve

theorem solution
    {L : Type*} [Field L] [Algebra ℚ L] (F₀ : IntermediateField ℚ (LaurentSeries ℚ))
    (σ : L ≃ₐ[ℚ] L) (z : laurentBaseChange L F₀)
    (hz : ∀ n : ℤ, σ (((z : laurentBaseChange L F₀) : LaurentSeries L).coeff n) = ((z : laurentBaseChange L F₀) : LaurentSeries L).coeff n) :
    arithmeticGalois F₀ σ • z = z := by
  apply Subtype.ext
  rw [coe_arithmeticGalois_smul]
  ext n
  rw [coeffMap_coeff]
  exact hz n
