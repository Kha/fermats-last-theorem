import Mathlib
import Definitions.Def_ModularCurve_TateSlots
import P2M.Util
import P2M.Sol.S_ModularCurve_map_slotSubst

set_option autoImplicit false

theorem ModularCurve.map_slotSubst
    {A B : Type} [CommRing A] [CommRing B] (g : A →+* B) (p : ℕ) (c : Aˣ) (j : ℕ) (hj : 0 < j) (hjp : j < p)
    (f : MvPowerSeries (Fin 2) ℤ) :
    (ModularCurve.slotSubst A p c j f).map g = ModularCurve.slotSubst B p (Units.map (g : A →* B) c) j f := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_map_slotSubst.solution
