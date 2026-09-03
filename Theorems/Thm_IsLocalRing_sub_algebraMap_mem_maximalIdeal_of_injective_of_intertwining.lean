import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.Algebra.Algebra.Tower
import P2M.Util
import P2M.Sol.S_IsLocalRing_sub_algebraMap_mem_maximalIdeal_of_injective_of_intertwining

set_option autoImplicit false

theorem IsLocalRing.sub_algebraMap_mem_maximalIdeal_of_injective_of_intertwining
    {𝒪 : Type} [CommRing 𝒪] [IsLocalRing 𝒪] [IsNoetherianRing 𝒪]
    {R₀ Rₐ : Type} [CommRing R₀] [IsLocalRing R₀] [Algebra 𝒪 R₀] [Module.Finite 𝒪 R₀]
    [CommRing Rₐ] [IsLocalRing Rₐ] [Algebra 𝒪 Rₐ]
    {C₀ Cₐ : Type} [AddCommGroup C₀] [Module 𝒪 C₀] [Module R₀ C₀] [IsScalarTower 𝒪 R₀ C₀]
    [AddCommGroup Cₐ] [Module 𝒪 Cₐ] [Module Rₐ Cₐ] [IsScalarTower 𝒪 Rₐ Cₐ] [Module.Finite 𝒪 Cₐ]
    (F : C₀ →ₗ[𝒪] Cₐ) (hF : Function.Injective F) (m₀ : C₀) (hm₀ : m₀ ≠ 0)
    (x : R₀) (y : Rₐ) (u : 𝒪) (hx : x - algebraMap 𝒪 R₀ u ∈ IsLocalRing.maximalIdeal R₀)
    (hxy : ∀ m : C₀, F (x • m) = y • F m) :
    y - algebraMap 𝒪 Rₐ u ∈ IsLocalRing.maximalIdeal Rₐ := by p2m_exact_reverting @_root_.P2MW.S_IsLocalRing_sub_algebraMap_mem_maximalIdeal_of_injective_of_intertwining.solution
