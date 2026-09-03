import Mathlib
import Definitions.Def_Dieudonne_DatumAndHonda
import Definitions.Def_Dieudonne_WittVectorHom
import Definitions.Def_Dieudonne_WittHomColimit
import Definitions.Def_Dieudonne_FontaineHodge
import Definitions.Def_Dieudonne_UnipotentWittCovector
import Definitions.Def_Dieudonne_FontaineFunctor
import Definitions.Def_MvFormalGroup_BasicV2
import Definitions.Def_MvFormalGroup_EndRingV2
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_PointsV2
import P2M.Util
import P2M.Sol.S_Deformation_FontaineLift_isPadicLimit_wPartialSum_adicEval

universe u v

theorem Deformation.FontaineLift.isPadicLimit_wPartialSum_adicEval
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] {d : ℕ}
    (a : ℕ → MvPowerSeries (Fin d) 𝓞) (ha : ∀ n, MvPowerSeries.constantCoeff (a n) = 0)
    (g : Type v) [CommRing g] [Algebra 𝓞 g] [IsAdicComplete (Ideal.span {(p : g)}) g]
    (x : Fin d → g) (hx : ∀ j, x j ∈ (Ideal.span {(p : g)}).radical) :
    Deformation.PLoc.IsPadicLimit p
      (Deformation.PLoc.wPartialSum p fun n => MvFormalGroup.adicEval (Ideal.span {(p : g)}) x (a n))
      (Deformation.PLoc.wSeries p fun n => MvFormalGroup.adicEval (Ideal.span {(p : g)}) x (a n)) := by p2m_exact_reverting @_root_.P2MW.S_Deformation_FontaineLift_isPadicLimit_wPartialSum_adicEval.solution
