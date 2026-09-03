import Mathlib
import Definitions.Def_GaloisRep_ModThreeCyclotomic
import P2M.Util
import P2M.Sol.S_GaloisRep_isTotallyComplex_of_fixingSubgroup_le_ker_of_det_eq_modThreeCyclotomicChar
attribute [-simp] ExtCitation.archimedeanLoc_archimedeanGen complexConjAlgEquiv_apply

theorem GaloisRep.isTotallyComplex_of_fixingSubgroup_le_ker_of_det_eq_modThreeCyclotomicChar
    (ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3))
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ F] [IsGalois ℚ F]
    (hfix : F.fixingSubgroup ≤ ρ.ker)
    (hdet : Matrix.GeneralLinearGroup.det.comp ρ = WeierstrassCurve.modThreeCyclotomicChar) :
    NumberField.IsTotallyComplex F := by p2m_exact_reverting @_root_.P2MW.S_GaloisRep_isTotallyComplex_of_fixingSubgroup_le_ker_of_det_eq_modThreeCyclotomicChar.solution
