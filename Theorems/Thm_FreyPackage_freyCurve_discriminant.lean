import Mathlib
import Definitions.Def_FLTPrelim_FreyPackage
import P2M.Util
import P2M.Sol.S_FreyPackage_freyCurve_discriminant

open WeierstrassCurve
theorem FreyPackage.freyCurve_discriminant (P : FreyPackage) : P.freyCurve.Δ = (P.a * P.b * P.c) ^ (2 * P.p) / 2 ^ 8 := by p2m_exact_reverting @_root_.P2MW.S_FreyPackage_freyCurve_discriminant.solution
