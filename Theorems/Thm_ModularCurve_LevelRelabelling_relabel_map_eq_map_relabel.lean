import Mathlib
import Definitions.Def_ModularCurve_KatzLevelP
import Definitions.Def_ModularCurve_LevelRelabelling
import P2M.Util
import P2M.Sol.S_ModularCurve_LevelRelabelling_relabel_map_eq_map_relabel

set_option autoImplicit false

universe u

open ModularCurve ModularCurve.LevelRelabelling
open scoped Classical

theorem ModularCurve.LevelRelabelling.relabel_map_eq_map_relabel
    {T T' : Type u} [Field T] [Field T'] (f : T →+* T')
    (W : WeierstrassCurve T) (g : Matrix (Fin 2) (Fin 2) ℤ) (D : ModularCurve.LevelPData T) :
    LevelPData.relabel (W.map f) g (D.map f) = (LevelPData.relabel W g D).map f := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_LevelRelabelling_relabel_map_eq_map_relabel.solution
