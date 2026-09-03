import Mathlib
import P2M.Util
import P2M.Sol.S_ringKrullDim_localization_eq_one_of_isPrincipalIdealRing_of_flat

theorem ringKrullDim_localization_eq_one_of_isPrincipalIdealRing_of_flat
    (D : Type*) {C : Type*} [CommRing D] [IsDomain D] [IsPrincipalIdealRing D] (hD : ¬ IsField D)
    [CommRing C] [Algebra D C] [Module.Finite D C] [Module.Flat D C]
    (m : Ideal C) [m.IsMaximal] :
    ringKrullDim (Localization.AtPrime m) = 1 := by p2m_exact_reverting @_root_.P2MW.S_ringKrullDim_localization_eq_one_of_isPrincipalIdealRing_of_flat.solution
