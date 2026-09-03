import Mathlib
import P2M.Util
import P2M.Sol.S_Module_Invertible_of_localization_maximal

set_option autoImplicit false

open scoped TensorProduct

theorem Module.Invertible.of_localization_maximal
    {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M] [Module.FinitePresentation R M]
    (H : ∀ (P : Ideal R) [P.IsMaximal], Module.Invertible (Localization.AtPrime P) (LocalizedModule P.primeCompl M)) :
    Module.Invertible R M := by p2m_exact_reverting @_root_.P2MW.S_Module_Invertible_of_localization_maximal.solution
