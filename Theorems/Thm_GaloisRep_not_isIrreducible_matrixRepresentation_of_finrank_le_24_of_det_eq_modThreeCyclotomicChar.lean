import Mathlib
import Definitions.Def_Deformations_MatrixRepresentation
import Definitions.Def_GaloisRep_ModThreeCyclotomic
import P2M.Util
import P2M.Sol.S_GaloisRep_not_isIrreducible_matrixRepresentation_of_finrank_le_24_of_det_eq_modThreeCyclotomicChar
attribute [-simp] ExtCitation.archimedeanLoc_archimedeanGen complexConjAlgEquiv_apply

theorem GaloisRep.not_isIrreducible_matrixRepresentation_of_finrank_le_24_of_det_eq_modThreeCyclotomicChar
    (ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3))
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ F] [IsGalois ℚ F]
    (hfix : F.fixingSubgroup = ρ.ker)
    (h24 : Module.finrank ℚ F ≤ 24)
    (hunr : ∀ (P : Ideal (NumberField.RingOfIntegers F)) [P.IsMaximal],
      (3 : NumberField.RingOfIntegers F) ∉ P → Algebra.IsUnramifiedAt ℤ P)
    (hdet : Matrix.GeneralLinearGroup.det.comp ρ = WeierstrassCurve.modThreeCyclotomicChar) :
    ¬ Representation.IsIrreducible (Deformation.matrixRepresentation ρ) := by p2m_exact_reverting @_root_.P2MW.S_GaloisRep_not_isIrreducible_matrixRepresentation_of_finrank_le_24_of_det_eq_modThreeCyclotomicChar.solution
