import Mathlib
import P2M.Util
import P2M.Sol.S_Matrix_isUnit_of_isUnit_map_of_le_jacobson_bot

universe u v

theorem Matrix.isUnit_of_isUnit_map_of_le_jacobson_bot
    {S : Type u} [CommRing S] {n : Type v} [Fintype n] [DecidableEq n]
    (𝔫 : Ideal S) (h𝔫 : 𝔫 ≤ (⊥ : Ideal S).jacobson)
    (A : Matrix n n S) (hA : IsUnit (A.map (Ideal.Quotient.mk 𝔫))) :
    IsUnit A := by p2m_exact_reverting @_root_.P2MW.S_Matrix_isUnit_of_isUnit_map_of_le_jacobson_bot.solution
