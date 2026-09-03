import Mathlib
import Definitions.Def_ModularCurve_ArithmeticGalois
import P2M.Util
import P2M.Sol.S_ModularCurve_arithmeticGalois_smul_eq_self_of_forall_coeff_eq

set_option autoImplicit false

open ModularCurve

theorem ModularCurve.arithmeticGalois_smul_eq_self_of_forall_coeff_eq
    {L : Type*} [Field L] [Algebra ℚ L] (F₀ : IntermediateField ℚ (LaurentSeries ℚ))
    (σ : L ≃ₐ[ℚ] L) (z : laurentBaseChange L F₀)
    (hz : ∀ n : ℤ, σ (((z : laurentBaseChange L F₀) : LaurentSeries L).coeff n) = ((z : laurentBaseChange L F₀) : LaurentSeries L).coeff n) :
    arithmeticGalois F₀ σ • z = z := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_arithmeticGalois_smul_eq_self_of_forall_coeff_eq.solution
