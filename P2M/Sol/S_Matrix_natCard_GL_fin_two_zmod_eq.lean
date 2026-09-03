import Mathlib
import P2M.Util
namespace P2MW.S_Matrix_natCard_GL_fin_two_zmod_eq

set_option autoImplicit false

theorem solution (p : ℕ) [Fact p.Prime] :
    Nat.card (GL (Fin 2) (ZMod p)) = (p ^ 2 - 1) * (p ^ 2 - p) := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  rw [Matrix.card_GL_field]
  simp [Fin.prod_univ_two, ZMod.card]
