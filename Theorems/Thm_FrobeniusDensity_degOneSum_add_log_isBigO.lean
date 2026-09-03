import Definitions.Def_FrobeniusDensity_PrimeSums
import P2M.Util
import P2M.Sol.S_FrobeniusDensity_degOneSum_add_log_isBigO

open Filter Topology Asymptotics
theorem FrobeniusDensity.degOneSum_add_log_isBigO
    (K : Type*) [Field K] [NumberField K] (S₀ : Finset ℕ) :
    (fun s : ℝ => (∑' ℓ : ℕ, (if ℓ ∈ S₀ then 0 else
        (FrobeniusDensity.degOneCount K ℓ : ℝ)) * (ℓ : ℝ) ^ (-s))
      + Real.log (s - 1)) =O[nhdsWithin 1 (Set.Ioi 1)] (fun _ => (1 : ℝ)) := by p2m_exact_reverting @_root_.P2MW.S_FrobeniusDensity_degOneSum_add_log_isBigO.solution
