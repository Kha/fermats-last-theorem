import Mathlib
import P2M.Util
import P2M.Sol.S_AdicCompletion_isAdicComplete_map_algebraMap_of_fg

set_option autoImplicit false

universe u

theorem AdicCompletion.isAdicComplete_map_algebraMap_of_fg
    {B : Type u} [CommRing B] (I : Ideal B) (hI : I.FG) :
    IsAdicComplete (I.map (algebraMap B (AdicCompletion I B))) (AdicCompletion I B) := by p2m_exact_reverting @_root_.P2MW.S_AdicCompletion_isAdicComplete_map_algebraMap_of_fg.solution
