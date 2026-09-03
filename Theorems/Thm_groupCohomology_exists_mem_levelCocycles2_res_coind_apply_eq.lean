import Mathlib
import Definitions.Def_GroupCohomology_ContinuousH2
import P2M.Util
import P2M.Sol.S_groupCohomology_exists_mem_levelCocycles2_res_coind_apply_eq
attribute [-instance] groupCohomology.normal_comap_fixingSubgroup groupCohomology.finiteIndex_comap_fixingSubgroup
attribute [-simp] groupCohomology.cochainsPullPush₁_apply groupCohomology.cochainsPullPush₂_apply groupCohomology.coe_levelCocycles₂Map groupCohomology.continuousH2Map_continuousH2π

set_option autoImplicit false

universe u

open CategoryTheory

theorem groupCohomology.exists_mem_levelCocycles2_res_coind_apply_eq
    {k : Type u} [CommRing k] {V : Type u} [AddCommGroup V] [Module k V]
    {G : Type u} [Group G] (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (U : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) [U.Normal]
    (hU : ∃ F₀ : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F₀ ∧ F₀.fixingSubgroup ≤ U)
    (γ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ⧸ (U ⊔ r.range) → (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (hγ : ∀ t, (γ t : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ⧸ (U ⊔ r.range)) = t)
    (b : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ⧸ (U ⊔ r.range) → ↥(U.comap r) × ↥(U.comap r) → V)
    (hb : ∀ t, b t ∈ groupCohomology.levelCocycles₂ (r.comp (U.comap r).subtype) (Rep.trivial k ↥(U.comap r) V)) :
    ∃ c : G × G → Rep.res r (Rep.coind U.subtype (Rep.trivial k ↥U V)),
      c ∈ groupCohomology.levelCocycles₂ r (Rep.res r (Rep.coind U.subtype (Rep.trivial k ↥U V))) ∧
      ∀ (t : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ⧸ (U ⊔ r.range)) (d d' : ↥(U.comap r)),
        ((c ((d : G), (d' : G)) : Rep.coind U.subtype (Rep.trivial k ↥U V)) :
          (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → V) (γ t) = b t (d, d') := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_exists_mem_levelCocycles2_res_coind_apply_eq.solution
