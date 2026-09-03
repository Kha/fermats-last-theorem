import Mathlib
import Definitions.Def_ModularCurve_ArithmeticGalois
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_algEquiv_laurentBaseChange_coeffMap_eq_of_arithmeticGalois_comm

set_option autoImplicit false

open ModularCurve

theorem ModularCurve.exists_algEquiv_laurentBaseChange_coeffMap_eq_of_arithmeticGalois_comm
    (F : IntermediateField ℚ (LaurentSeries ℚ))
    (L : Type) [Field L] [CharZero L] (ιA : L →+* AlgebraicClosure ℚ)
    (θ : ↥(laurentBaseChange (AlgebraicClosure ℚ) F) ≃ₐ[AlgebraicClosure ℚ] ↥(laurentBaseChange (AlgebraicClosure ℚ) F))
    (hθgal : ∀ τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, (∀ x : L, τ (ιA x) = ιA x) →
        ∀ g : ↥(laurentBaseChange (AlgebraicClosure ℚ) F),
          θ (arithmeticGalois F τ • g) = arithmeticGalois F τ • θ g) :
    ∃ σ : ↥(laurentBaseChange L F) ≃ₐ[L] ↥(laurentBaseChange L F),
      ∀ (f : ↥(laurentBaseChange L F)) (g : ↥(laurentBaseChange (AlgebraicClosure ℚ) F)),
        (g : LaurentSeries (AlgebraicClosure ℚ)) = coeffMap ιA (f : LaurentSeries L) →
          ((θ g : ↥(laurentBaseChange (AlgebraicClosure ℚ) F)) : LaurentSeries (AlgebraicClosure ℚ)) =
            coeffMap ιA ((σ f : ↥(laurentBaseChange L F)) : LaurentSeries L) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_algEquiv_laurentBaseChange_coeffMap_eq_of_arithmeticGalois_comm.solution
