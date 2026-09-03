import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.Finiteness.Defs
import P2M.Util
import P2M.Sol.S_IsLocalRing_of_isDomain_of_module_finite_of_isAdicComplete

open IsLocalRing Polynomial
open scoped TensorProduct

theorem IsLocalRing.of_isDomain_of_module_finite_of_isAdicComplete
    {R S : Type} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    [CommRing S] [IsDomain S] [Algebra R S] [Module.Finite R S] : IsLocalRing S := by p2m_exact_reverting @_root_.P2MW.S_IsLocalRing_of_isDomain_of_module_finite_of_isAdicComplete.solution
