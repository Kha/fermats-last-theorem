import Definitions.Def_FrobeniusDensity_PrimeSums
import P2M.Util
import P2M.Sol.S_FrobeniusDensity_primeSum_toReal_add_log_isBigO

open Filter Topology Asymptotics
theorem FrobeniusDensity.primeSum_toReal_add_log_isBigO
    (K : Type*) [Field K] [NumberField K] :
    (fun s : ℝ => (FrobeniusDensity.primeSum K s).toReal + Real.log (s - 1))
      =O[nhdsWithin 1 (Set.Ioi 1)] (fun _ => (1:ℝ)) := by p2m_exact_reverting @_root_.P2MW.S_FrobeniusDensity_primeSum_toReal_add_log_isBigO.solution
