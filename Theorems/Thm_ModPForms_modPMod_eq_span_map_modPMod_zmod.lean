import Definitions.Def_CuspForm_ModPForms
import Mathlib.Algebra.Field.ZMod
import P2M.Util
import P2M.Sol.S_ModPForms_modPMod_eq_span_map_modPMod_zmod
set_option autoImplicit false
theorem ModPForms.modPMod_eq_span_map_modPMod_zmod (p : ℕ) [Fact p.Prime] (N : ℕ) (k : ℤ) (F : Type) [Field F] [CharP F p] :
    ModPForms.modPMod N k F =
      Submodule.span F (PowerSeries.map (ZMod.castHom (dvd_refl p) F) ''
        (ModPForms.modPMod N k (ZMod p) : Set (PowerSeries (ZMod p)))) := by p2m_exact_reverting @_root_.P2MW.S_ModPForms_modPMod_eq_span_map_modPMod_zmod.solution
