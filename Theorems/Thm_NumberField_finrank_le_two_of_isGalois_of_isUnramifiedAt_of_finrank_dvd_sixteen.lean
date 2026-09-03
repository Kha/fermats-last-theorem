import Mathlib
import P2M.Util
import P2M.Sol.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen

theorem NumberField.finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ F] [IsGalois ℚ F]
    (hunr : ∀ (P : Ideal (NumberField.RingOfIntegers F)) [P.IsMaximal],
      (3 : NumberField.RingOfIntegers F) ∉ P → Algebra.IsUnramifiedAt ℤ P)
    (hdvd : Module.finrank ℚ F ∣ 16) :
    Module.finrank ℚ F ≤ 2 := by p2m_exact_reverting @_root_.P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.solution
