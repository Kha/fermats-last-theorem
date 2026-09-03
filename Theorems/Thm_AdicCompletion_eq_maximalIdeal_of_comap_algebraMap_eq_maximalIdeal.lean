import Mathlib
import Definitions.Def_AdicCompletionLocalRing
import P2M.Util
import P2M.Sol.S_AdicCompletion_eq_maximalIdeal_of_comap_algebraMap_eq_maximalIdeal

set_option autoImplicit false

open IsLocalRing

theorem AdicCompletion.eq_maximalIdeal_of_comap_algebraMap_eq_maximalIdeal
    (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (P : Ideal (AdicCompletion (maximalIdeal R) R)) [P.IsPrime]
    (hP : Ideal.comap (algebraMap R (AdicCompletion (maximalIdeal R) R)) P = maximalIdeal R) :
    P = maximalIdeal (AdicCompletion (maximalIdeal R) R) := by p2m_exact_reverting @_root_.P2MW.S_AdicCompletion_eq_maximalIdeal_of_comap_algebraMap_eq_maximalIdeal.solution
