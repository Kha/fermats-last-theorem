import Definitions.Def_FrobeniusDensity_PrimeSums
import P2M.Util
import P2M.Sol.S_FrobeniusDensity_summable_degOne_term

theorem FrobeniusDensity.summable_degOne_term
    (K : Type*) [Field K] [NumberField K] (S₀ : Finset ℕ) {s : ℝ} (hs : 1 < s) :
    Summable (fun ℓ : ℕ => (if ℓ ∈ S₀ then 0 else
      (FrobeniusDensity.degOneCount K ℓ : ℝ)) * (ℓ : ℝ) ^ (-s)) := by p2m_exact_reverting @_root_.P2MW.S_FrobeniusDensity_summable_degOne_term.solution
