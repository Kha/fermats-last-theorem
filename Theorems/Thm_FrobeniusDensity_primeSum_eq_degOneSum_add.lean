import Definitions.Def_FrobeniusDensity_PrimeSums
import P2M.Util
import P2M.Sol.S_FrobeniusDensity_primeSum_eq_degOneSum_add

theorem FrobeniusDensity.primeSum_eq_degOneSum_add
    (K : Type*) [Field K] [NumberField K] (S₀ : Finset ℕ) (s : ℝ) :
    FrobeniusDensity.primeSum K s =
      FrobeniusDensity.degOneSum K S₀ s + FrobeniusDensity.cutSum K S₀ s +
      FrobeniusDensity.tailSum K s := by p2m_exact_reverting @_root_.P2MW.S_FrobeniusDensity_primeSum_eq_degOneSum_add.solution
