import Mathlib
import Definitions.Def_ModularCurve_X1HeckeModule
import Definitions.Def_ModularCurve_X1DegeneracyPullback
import P2M.Util
import P2M.Sol.S_ModularCurve_JOne_degeneracyPullbackPair_comm_diamondOneBar

set_option autoImplicit false

theorem ModularCurve.JOne.degeneracyPullbackPair_comm_diamondOneBar
    (N : ℕ) [NeZero N] (ℓ : ℕ) [NeZero ℓ] (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N)
    (N' : ℕ) (hN' : N' = N * ℓ)
    (hin : ModularCurve.HeckeDiamondInputsAll N) (hin' : ModularCurve.HeckeDiamondInputsAll N')
    (i : Fin 2) (x : ModularCurve.JOne N) :
    ∀ d : ℕ, ¬ ℓ ∣ d →
      ModularCurve.JOne.degeneracyPullbackPair N N' ℓ i (ModularCurve.diamondOneBar N d x) =
        ModularCurve.diamondOneBar N' d (ModularCurve.JOne.degeneracyPullbackPair N N' ℓ i x) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_JOne_degeneracyPullbackPair_comm_diamondOneBar.solution
