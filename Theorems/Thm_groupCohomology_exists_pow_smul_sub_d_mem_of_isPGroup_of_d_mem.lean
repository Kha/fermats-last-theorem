import Mathlib
import P2M.Util
import P2M.Sol.S_groupCohomology_exists_pow_smul_sub_d_mem_of_isPGroup_of_d_mem

set_option autoImplicit false
open CategoryTheory groupCohomology

theorem groupCohomology.exists_pow_smul_sub_d_mem_of_isPGroup_of_d_mem
    {G : Type} [Group G] [Finite G] (p : ℕ) [Fact p.Prime] (hG : IsPGroup p G)
    (A : Rep.{0} ℤ G) (W : AddSubgroup A) (hW : ∀ (g : G) (a : A), a ∈ W → A.ρ g a ∈ W) [W.FiniteIndex]
    (ν : (Fin 1 → G) → A)
    (hν : ∀ g : Fin 2 → G, ((inhomogeneousCochains A).d 1 2).hom ν g ∈ W) :
    ∃ (m : (Fin 0 → G) → A) (k : ℕ),
      ∀ g : Fin 1 → G, (p ^ k : ℤ) • (ν g - ((inhomogeneousCochains A).d 0 1).hom m g) ∈ W := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_exists_pow_smul_sub_d_mem_of_isPGroup_of_d_mem.solution
