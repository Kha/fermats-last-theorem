import Mathlib
import Definitions.Def_GaloisRep_GlobalUnramifiedAt
import Definitions.Def_Deformations_MatrixRepresentation
import Definitions.Def_GaloisRep_ModThreeCyclotomic
import P2M.Util
import P2M.Sol.S_GaloisRep_not_isIrreducible_matrixRepresentation_of_isUnramifiedAt_of_det_eq_modThreeCyclotomicChar
attribute [-simp] ExtCitation.archimedeanLoc_archimedeanGen complexConjAlgEquiv_apply

theorem GaloisRep.not_isIrreducible_matrixRepresentation_of_isUnramifiedAt_of_det_eq_modThreeCyclotomicChar
    (ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3))
    (M : IntermediateField ℚ (AlgebraicClosure ℚ)) (hM : FiniteDimensional ℚ M)
    (hker : M.fixingSubgroup ≤ ρ.ker)
    (hunr : ∀ q : ℕ, q.Prime → q ≠ 3 → GlobalGaloisRep.IsUnramifiedAt ρ q)
    (hdet : Matrix.GeneralLinearGroup.det.comp ρ = WeierstrassCurve.modThreeCyclotomicChar) :
    ¬ Representation.IsIrreducible (Deformation.matrixRepresentation ρ) := by p2m_exact_reverting @_root_.P2MW.S_GaloisRep_not_isIrreducible_matrixRepresentation_of_isUnramifiedAt_of_det_eq_modThreeCyclotomicChar.solution
