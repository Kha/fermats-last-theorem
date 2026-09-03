import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Jacobson.Ideal
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import P2M.Util
import P2M.Sol.S_IsLocalRing_map_maximalIdeal_le_jacobson_bot_of_isIntegral

theorem IsLocalRing.map_maximalIdeal_le_jacobson_bot_of_isIntegral {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [IsLocalRing R] [Algebra.IsIntegral R S] :
    (IsLocalRing.maximalIdeal R).map (algebraMap R S) ≤ Ideal.jacobson (⊥ : Ideal S) := by p2m_exact_reverting @_root_.P2MW.S_IsLocalRing_map_maximalIdeal_le_jacobson_bot_of_isIntegral.solution
