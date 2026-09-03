import Mathlib
import P2M.Util
import P2M.Sol.S_IsLocalRing_exists_isLocalRing_adicCompletion_isAdicComplete_map_maximalIdeal_eq

set_option autoImplicit false

universe u

open IsLocalRing in

theorem IsLocalRing.exists_isLocalRing_adicCompletion_isAdicComplete_map_maximalIdeal_eq
    (O : Type u) [CommRing O] [IsNoetherianRing O] [IsLocalRing O] :
    ∃ (_ : IsLocalRing (AdicCompletion (maximalIdeal O) O))
      (_ : IsLocalHom (algebraMap O (AdicCompletion (maximalIdeal O) O))),
      IsAdicComplete (maximalIdeal (AdicCompletion (maximalIdeal O) O)) (AdicCompletion (maximalIdeal O) O) ∧
      Ideal.map (algebraMap O (AdicCompletion (maximalIdeal O) O)) (maximalIdeal O) =
        maximalIdeal (AdicCompletion (maximalIdeal O) O) ∧
      ∀ x : AdicCompletion (maximalIdeal O) O, ∃ o : O,
        x - algebraMap O (AdicCompletion (maximalIdeal O) O) o ∈ maximalIdeal (AdicCompletion (maximalIdeal O) O) := by p2m_exact_reverting @_root_.P2MW.S_IsLocalRing_exists_isLocalRing_adicCompletion_isAdicComplete_map_maximalIdeal_eq.solution
