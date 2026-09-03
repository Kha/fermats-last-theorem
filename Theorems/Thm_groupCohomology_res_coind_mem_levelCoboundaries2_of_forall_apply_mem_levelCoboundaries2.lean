import Mathlib
import Definitions.Def_GroupCohomology_ContinuousH2
import P2M.Util
import P2M.Sol.S_groupCohomology_res_coind_mem_levelCoboundaries2_of_forall_apply_mem_levelCoboundaries2
attribute [-instance] groupCohomology.normal_comap_fixingSubgroup groupCohomology.finiteIndex_comap_fixingSubgroup
attribute [-simp] groupCohomology.cochainsPullPush₁_apply groupCohomology.cochainsPullPush₂_apply groupCohomology.coe_levelCocycles₂Map groupCohomology.continuousH2Map_continuousH2π

set_option autoImplicit false

universe u

open CategoryTheory

theorem groupCohomology.res_coind_mem_levelCoboundaries2_of_forall_apply_mem_levelCoboundaries2
    {k : Type u} [CommRing k] {V : Type u} [AddCommGroup V] [Module k V]
    {G : Type u} [Group G] (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (U : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) [U.Normal]
    (hU : ∃ F₀ : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F₀ ∧ F₀.fixingSubgroup ≤ U)
    (γ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ⧸ (U ⊔ r.range) → (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (hγ : ∀ t, (γ t : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ⧸ (U ⊔ r.range)) = t)
    (c : G × G → Rep.res r (Rep.coind U.subtype (Rep.trivial k ↥U V)))
    (hc : c ∈ groupCohomology.levelCocycles₂ r (Rep.res r (Rep.coind U.subtype (Rep.trivial k ↥U V))))
    (h : ∀ t, (fun d : ↥(U.comap r) × ↥(U.comap r) =>
        ((c ((d.1 : G), (d.2 : G)) : Rep.coind U.subtype (Rep.trivial k ↥U V)) :
          (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → V) (γ t))
      ∈ groupCohomology.levelCoboundaries₂ (r.comp (U.comap r).subtype) (Rep.trivial k ↥(U.comap r) V)) :
    c ∈ groupCohomology.levelCoboundaries₂ r (Rep.res r (Rep.coind U.subtype (Rep.trivial k ↥U V))) := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_res_coind_mem_levelCoboundaries2_of_forall_apply_mem_levelCoboundaries2.solution
