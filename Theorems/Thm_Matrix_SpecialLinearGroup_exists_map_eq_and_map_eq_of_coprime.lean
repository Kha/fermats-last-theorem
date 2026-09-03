import Mathlib
import P2M.Util
import P2M.Sol.S_Matrix_SpecialLinearGroup_exists_map_eq_and_map_eq_of_coprime

open scoped MatrixGroups

theorem Matrix.SpecialLinearGroup.exists_map_eq_and_map_eq_of_coprime
    (m M : ℕ) [NeZero m] [NeZero M] (hmM : Nat.Coprime m M)
    (A : SL(2, ZMod m)) (B : SL(2, ZMod M)) :
    ∃ γ : SL(2, ℤ), Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod m)) γ = A ∧
      Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M)) γ = B := by p2m_exact_reverting @_root_.P2MW.S_Matrix_SpecialLinearGroup_exists_map_eq_and_map_eq_of_coprime.solution
