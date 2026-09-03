import Mathlib
import P2M.Util
import P2M.Sol.S_Matrix_GeneralLinearGroup_exists_subfield_specialLinearGroup_conj_le_of_dvd_card
attribute [-simp] ModularCurve.upperElem_zero ModularCurve.lowerElem_coe ModularCurve.lowerElem_zero ModularCurve.upperElem_coe

set_option autoImplicit false

open Matrix MatrixGroups

theorem Matrix.GeneralLinearGroup.exists_subfield_specialLinearGroup_conj_le_of_dvd_card
    {K : Type} [Field K] {p : ℕ} [Fact p.Prime] [CharP K p] (hp2 : p ≠ 2)
    (H : Subgroup (GL (Fin 2) K)) [Finite H] (hdvd : p ∣ Nat.card H)
    (hirr : ∀ v : Fin 2 → K, v ≠ 0 →
      ∃ h ∈ H, ((h : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ v ∉ K ∙ v) :
    (p = 3 ∧ ¬ 9 ∣ Nat.card H) ∨
    ∃ (F : Subfield K) (_ : Finite F) (g : GL (Fin 2) K),
      (∀ s : SL(2, F),
        g * (Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.map F.subtype s)) * g⁻¹ ∈ H) ∧
      (∀ h ∈ H, ∃ (a : K) (m : GL (Fin 2) F),
        ((g⁻¹ * h * g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
          a • ((Matrix.GeneralLinearGroup.map F.subtype m : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) := by p2m_exact_reverting @_root_.P2MW.S_Matrix_GeneralLinearGroup_exists_subfield_specialLinearGroup_conj_le_of_dvd_card.solution
