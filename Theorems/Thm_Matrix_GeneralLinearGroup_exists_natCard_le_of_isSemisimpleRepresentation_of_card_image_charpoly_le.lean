import Mathlib
import Definitions.Def_Deformations_MatrixRepresentation
import P2M.Util
import P2M.Sol.S_Matrix_GeneralLinearGroup_exists_natCard_le_of_isSemisimpleRepresentation_of_card_image_charpoly_le
attribute [-simp] ModularCurve.upperElem_zero ModularCurve.lowerElem_coe ModularCurve.lowerElem_zero ModularCurve.upperElem_coe

set_option autoImplicit false

open scoped MatrixGroups

theorem Matrix.GeneralLinearGroup.exists_natCard_le_of_isSemisimpleRepresentation_of_card_image_charpoly_le
    (η : ℝ) (hη : η < 1 / 2) (M : ℕ) :
    ∃ A : ℕ, ∀ (ℓ : ℕ) [Fact ℓ.Prime] (G : Subgroup (GL (Fin 2) (ZMod ℓ))),
      (Deformation.matrixRepresentation G.subtype).IsSemisimpleRepresentation →
      ∀ H : Finset (GL (Fin 2) (ZMod ℓ)), (↑H : Set (GL (Fin 2) (ZMod ℓ))) ⊆ G →
        (1 - η) * (Nat.card G : ℝ) ≤ H.card →
        (H.image fun h : GL (Fin 2) (ZMod ℓ) =>
            (h : Matrix (Fin 2) (Fin 2) (ZMod ℓ)).charpoly).card ≤ M →
          Nat.card G ≤ A := by p2m_exact_reverting @_root_.P2MW.S_Matrix_GeneralLinearGroup_exists_natCard_le_of_isSemisimpleRepresentation_of_card_image_charpoly_le.solution
