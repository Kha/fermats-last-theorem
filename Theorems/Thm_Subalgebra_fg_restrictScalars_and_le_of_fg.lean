import Mathlib
import P2M.Util
import P2M.Sol.S_Subalgebra_fg_restrictScalars_and_le_of_fg

set_option autoImplicit false

universe u

theorem Subalgebra.fg_restrictScalars_and_le_of_fg
    {A₀ A : Type u} [CommRing A₀] [CommRing A] [Algebra A₀ A]
    (T : Subalgebra A₀ A) (hT : T.FG) (T' : Subalgebra ↥T A) (hT' : T'.FG) :
    (T'.restrictScalars A₀).FG ∧ (T : Set A) ⊆ (T'.restrictScalars A₀ : Set A) := by p2m_exact_reverting @_root_.P2MW.S_Subalgebra_fg_restrictScalars_and_le_of_fg.solution
