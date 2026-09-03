import Mathlib
import P2M.Util
import P2M.Sol.S_Ideal_height_eq_one_of_ne_bot_of_not_isMaximal_of_ringKrullDim_le_two

set_option autoImplicit false

theorem Ideal.height_eq_one_of_ne_bot_of_not_isMaximal_of_ringKrullDim_le_two
    {R : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    (hdim : ringKrullDim R ≤ 2) (P : Ideal R) [P.IsPrime] (hP0 : P ≠ ⊥) (hPm : ¬ P.IsMaximal) :
    P.height = 1 := by p2m_exact_reverting @_root_.P2MW.S_Ideal_height_eq_one_of_ne_bot_of_not_isMaximal_of_ringKrullDim_le_two.solution
