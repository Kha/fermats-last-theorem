import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.Nilpotent.Defs
import Mathlib.RingTheory.Noetherian.Defs
import P2M.Util
import P2M.Sol.S_AlgHom_congruenceIdeal_ne_bot_of_isReduced

universe u v

theorem AlgHom.congruenceIdeal_ne_bot_of_isReduced
    {𝒪 : Type u} {T : Type v} [CommRing 𝒪] [IsDomain 𝒪]
    [CommRing T] [Algebra 𝒪 T] [Module.Finite 𝒪 T] [IsNoetherianRing T] [IsReduced T]
    (πT : T →ₐ[𝒪] 𝒪) :
    (RingHom.ker πT).annihilator.map πT ≠ ⊥ := by p2m_exact_reverting @_root_.P2MW.S_AlgHom_congruenceIdeal_ne_bot_of_isReduced.solution
