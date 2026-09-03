import Mathlib
import Definitions.Def_GroupCohomology_ContinuousH2
import Definitions.Def_GroupCohomology_ContinuousH1
import Definitions.Def_GroupCohomology_CupProduct
import P2M.Util
import P2M.Sol.S_groupCohomology_cup_deltaCochain0_add_cup02_deltaCochain1_mem_levelCoboundaries2

set_option autoImplicit false

universe u

open CategoryTheory
open groupCohomology
theorem groupCohomology.cup_deltaCochain0_add_cup02_deltaCochain1_mem_levelCoboundaries2
    {k G : Type u} [CommRing k] [Group G]
    (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    {M' M M'' D'' D D' N : Rep.{u} k G}
    (i : M' ⟶ M) (π : M ⟶ M'') (hπ : Function.Surjective π.hom)
    (hex : ∀ m : M, π.hom m = 0 ↔ ∃ m' : M', i.hom m' = m)
    (πD : D'' ⟶ D) (iD : D ⟶ D') (hiD : Function.Surjective iD.hom)
    (hexD : ∀ x : D, iD.hom x = 0 ↔ ∃ y : D'', πD.hom y = x)
    (φ' : M' →ₗ[k] D' →ₗ[k] N)
    (φ : M →ₗ[k] D →ₗ[k] N) (hφ : Rep.IsEquivariantBilinear M D N φ)
    (φ'' : M'' →ₗ[k] D'' →ₗ[k] N)
    (hcompat_i : ∀ (m' : M') (x : D), φ (i.hom m') x = φ' m' (iD.hom x))
    (hcompat_π : ∀ (m : M) (y : D''), φ m (πD.hom y) = φ'' (π.hom m) y)
    (c : M'') (hc : ∀ s, M''.ρ s c = c)
    (y : cocycles₁ D') (hy : IsLevelConstant₁ r (⇑y)) :
    (cupCochain φ' (deltaCochain₀ i π hπ c) (⇑y)
        + fun st => φ'' c (deltaCochain₁ πD iD hiD (⇑y) st))
      ∈ levelCoboundaries₂ r N := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_cup_deltaCochain0_add_cup02_deltaCochain1_mem_levelCoboundaries2.solution
