import Mathlib
import P2M.Util
import P2M.Sol.S_HenselianLocalRing_moduleFinite_localization_atPrime_of_quasiFiniteAt

set_option autoImplicit false

open IsLocalRing

universe u v

theorem HenselianLocalRing.moduleFinite_localization_atPrime_of_quasiFiniteAt
    {R : Type u} [CommRing R] [HenselianLocalRing R]
    {S : Type v} [CommRing S] [Algebra R S] [Algebra.FiniteType R S]
    (q : Ideal S) [q.IsPrime] (hq : q.comap (algebraMap R S) = maximalIdeal R) [Algebra.QuasiFiniteAt R q] :
    Module.Finite R (Localization.AtPrime q) := by p2m_exact_reverting @_root_.P2MW.S_HenselianLocalRing_moduleFinite_localization_atPrime_of_quasiFiniteAt.solution
