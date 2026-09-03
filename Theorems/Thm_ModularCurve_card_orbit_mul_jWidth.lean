import Mathlib
import Definitions.Def_ModularCurve_LegendreJ
import Definitions.Def_ModularCurve_JWidth
import P2M.Util
import P2M.Sol.S_ModularCurve_card_orbit_mul_jWidth

open ModularCurve
theorem ModularCurve.card_orbit_mul_jWidth {K : Type*} [Field K] [DecidableEq K] (h2 : (2 : K) ≠ 0)
    (h3 : (3 : K) ≠ 0) {t : K} (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    ({t, 1 - t, t⁻¹, 1 - t⁻¹, (1 - t)⁻¹, 1 - (1 - t)⁻¹} : Finset K).card * jWidth (legendreJ t)
      = 6 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_card_orbit_mul_jWidth.solution
