import Mathlib
import Definitions.Def_ModularCurve_KatzLevelP
import Definitions.Def_ModularCurve_KatzLevelPUniversal
import Definitions.Def_ModularCurve_KatzLevelPClassifyingMaps
import P2M.Util
import P2M.Sol.S_ModularCurve_LevelP_flat_univBasisRing_vcRing_borelRing

theorem ModularCurve.LevelP.flat_univBasisRing_vcRing_borelRing (p : ℕ) :
    Module.Flat ℤ (ModularCurve.LevelP.UnivBasisRing p) ∧
      Module.Flat (ModularCurve.LevelP.UnivBasisRing p) (ModularCurve.LevelP.VCRing p) ∧
        ∀ a : ℕ, Module.Flat (ModularCurve.LevelP.UnivBasisRing p) (ModularCurve.LevelP.BorelRing p a) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_LevelP_flat_univBasisRing_vcRing_borelRing.solution
