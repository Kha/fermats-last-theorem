import Mathlib.RingTheory.AdicCompletion.Functoriality
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Mathlib.RingTheory.Finiteness.Cardinality
import Mathlib.Algebra.Module.Projective
import Mathlib.Algebra.BigOperators.Pi
import P2M.Util
import P2M.Sol.S_Module_Finite_of_finite_quotient_map_maximalIdeal

universe u v
theorem Module.Finite.of_finite_quotient_map_maximalIdeal
    {𝒪 : Type u} {A : Type v} [CommRing 𝒪] [IsLocalRing 𝒪] [IsPrecomplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
    [CommRing A] [Algebra 𝒪 A] [IsLocalRing A] [IsHausdorff (IsLocalRing.maximalIdeal A) A]
    [IsLocalHom (algebraMap 𝒪 A)]
    (hfin : Module.Finite 𝒪 (A ⧸ (IsLocalRing.maximalIdeal 𝒪).map (algebraMap 𝒪 A))) :
    Module.Finite 𝒪 A := by p2m_exact_reverting @_root_.P2MW.S_Module_Finite_of_finite_quotient_map_maximalIdeal.solution
