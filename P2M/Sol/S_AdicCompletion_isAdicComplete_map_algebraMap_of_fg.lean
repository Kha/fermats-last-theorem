import Mathlib
import P2M.Util
namespace P2MW.S_AdicCompletion_isAdicComplete_map_algebraMap_of_fg

set_option autoImplicit false

universe u

theorem solution
    {B : Type u} [CommRing B] (I : Ideal B) (hI : I.FG) :
    IsAdicComplete (I.map (algebraMap B (AdicCompletion I B))) (AdicCompletion I B) := by
  rw [IsAdicComplete.map_algebraMap_iff]
  exact AdicCompletion.isAdicComplete hI
