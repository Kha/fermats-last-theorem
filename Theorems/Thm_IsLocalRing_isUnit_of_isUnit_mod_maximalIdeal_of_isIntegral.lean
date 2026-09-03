import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Jacobson.Ideal
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import P2M.Util
import P2M.Sol.S_IsLocalRing_isUnit_of_isUnit_mod_maximalIdeal_of_isIntegral

theorem IsLocalRing.isUnit_of_isUnit_mod_maximalIdeal_of_isIntegral {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [IsLocalRing R] [Algebra.IsIntegral R S] {a : S} (h : IsUnit ((Ideal.Quotient.mk ((IsLocalRing.maximalIdeal R).map (algebraMap R S))) a)) :
    IsUnit a := by p2m_exact_reverting @_root_.P2MW.S_IsLocalRing_isUnit_of_isUnit_mod_maximalIdeal_of_isIntegral.solution
