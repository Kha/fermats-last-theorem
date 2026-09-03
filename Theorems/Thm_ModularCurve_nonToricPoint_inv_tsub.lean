import Definitions.Def_ModularCurve_TateSlots
import P2M.Util
import P2M.Sol.S_ModularCurve_nonToricPoint_inv_tsub

open ModularCurve

theorem ModularCurve.nonToricPoint_inv_tsub {K : Type*} [CommRing K] (p : ℕ) (c : Kˣ) (j : ℕ)
    (hj : 0 < j) (hjp : j < p) :
    nonToricPoint K p c⁻¹ (p - j) =
      ((nonToricPoint K p c j).1, -(nonToricPoint K p c j).2 - (nonToricPoint K p c j).1) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_nonToricPoint_inv_tsub.solution
