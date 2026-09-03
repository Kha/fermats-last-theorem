import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.Algebra.Algebra.Tower
import P2M.Util
import P2M.Sol.S_IsLocalRing_map_mem_of_forall_generalized_eigenvector_mem_of_forall_exists_partner

set_option autoImplicit false

theorem IsLocalRing.map_mem_of_forall_generalized_eigenvector_mem_of_forall_exists_partner
    {𝒪 : Type} [CommRing 𝒪] [IsLocalRing 𝒪]
    {R 𝕋 : Type} [CommRing R] [IsLocalRing R] [CommRing 𝕋] [Algebra 𝒪 R] [Algebra 𝒪 𝕋]
    [Module.Finite 𝒪 R]
    {C V : Type} [AddCommGroup C] [Module 𝒪 C] [Module R C] [IsScalarTower 𝒪 R C]
    [AddCommGroup V] [Module 𝒪 V] [Module 𝕋 V] [IsScalarTower 𝒪 𝕋 V]
    (j : C →ₗ[𝒪] V) (W : Submodule 𝕋 V)
    {G : Type} (cond : G → Prop) (t : G → 𝕋) (c : G → 𝒪)
    (hfull : ∀ v : V, (∀ g, cond g → ∀ k : ℕ, ∃ n : ℕ,
      ((t g - algebraMap 𝒪 𝕋 (c g)) ^ n) • v ∈ ((IsLocalRing.maximalIdeal 𝒪) ^ k • ⊤ : Submodule 𝒪 V)) → v ∈ W)
    (hpart : ∀ g, cond g → ∃ y : R, y - algebraMap 𝒪 R (c g) ∈ IsLocalRing.maximalIdeal R ∧
      ∀ m : C, j (y • m) = t g • j m) :
    ∀ m : C, j m ∈ W := by p2m_exact_reverting @_root_.P2MW.S_IsLocalRing_map_mem_of_forall_generalized_eigenvector_mem_of_forall_exists_partner.solution
