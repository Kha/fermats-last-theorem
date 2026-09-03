import Definitions.Def_ModularCurve_TateSlots
import Definitions.Def_WeierstrassCurve_Velu
import Definitions.Def_ModularCurve_PhiGen
import P2M.Util
import P2M.Sol.S_ModularCurve_veluQuotient_nonToricSlotSet

open ModularCurve
theorem ModularCurve.veluQuotient_nonToricSlotSet (K : Type*) [CommRing K] (p : ℕ) [NeZero p]
    (hp : Odd p) (ζ : Kˣ) (hζ : ζ ^ p = 1) (b : ℕ)
    (hE : tateUnivCurve.toAffine.Equation tateUnivX tateUnivY) :
    (tateBase K p).veluQuotient (nonToricSlotSet K p ζ b) =
      (tateLaurent K).map (qTwist (ζ ^ b)) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_veluQuotient_nonToricSlotSet.solution
