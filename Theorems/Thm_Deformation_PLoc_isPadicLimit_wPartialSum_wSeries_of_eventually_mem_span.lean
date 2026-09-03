import Mathlib
import Definitions.Def_Dieudonne_DatumAndHonda
import Definitions.Def_Dieudonne_WittVectorHom
import Definitions.Def_Dieudonne_WittHomColimit
import Definitions.Def_Dieudonne_FontaineHodge
import Definitions.Def_Dieudonne_UnipotentWittCovector
import Definitions.Def_Dieudonne_FontaineFunctor
import P2M.Util
import P2M.Sol.S_Deformation_PLoc_isPadicLimit_wPartialSum_wSeries_of_eventually_mem_span

universe u

theorem Deformation.PLoc.isPadicLimit_wPartialSum_wSeries_of_eventually_mem_span
    (p : ℕ) [Fact p.Prime] (g : Type u) [CommRing g] [IsAdicComplete (Ideal.span {(p : g)}) g]
    (c : ℕ → g) (hc : ∃ n : ℕ, ∀ k, n ≤ k → c k ∈ Ideal.span {(p : g)}) :
    Deformation.PLoc.IsPadicLimit p (Deformation.PLoc.wPartialSum p c) (Deformation.PLoc.wSeries p c) := by p2m_exact_reverting @_root_.P2MW.S_Deformation_PLoc_isPadicLimit_wPartialSum_wSeries_of_eventually_mem_span.solution
