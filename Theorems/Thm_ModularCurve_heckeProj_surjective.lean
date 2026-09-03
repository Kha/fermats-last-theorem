import Definitions.Def_HeckeGalois_EichlerShimura
import Definitions.Def_ModularCurve_HeckeProj
import P2M.Util
import P2M.Sol.S_ModularCurve_heckeProj_surjective

open ModularCurve

theorem ModularCurve.heckeProj_surjective (p : ℕ) [NeZero p] : Function.Surjective (heckeProj p) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_heckeProj_surjective.solution
