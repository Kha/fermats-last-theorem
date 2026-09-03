import Mathlib
import Definitions.Def_GroupCohomology_ContinuousH2
import Definitions.Def_GroupCohomology_ContinuousH2Map
import Definitions.Def_GroupCohomology_ContinuousH1
import P2M.Util
import P2M.Sol.S_groupCohomology_finrank_euler_coind_res_index_eq_mul

set_option autoImplicit false

universe u

open CategoryTheory
theorem groupCohomology.finrank_euler_coind_res_index_eq_mul {k G : Type u} [Field k] [Group G] (p : ℕ) [Fact p.Prime] [CharP k p]
    (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (S : Subgroup G)
    (HFIN : ∀ (M : Rep.{u} k S), (∀ m : M, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
          ∀ s : S, (r.comp S.subtype) s ∈ F.fixingSubgroup → M.ρ s m = m) → FiniteDimensional k M →
        FiniteDimensional k (groupCohomology.continuousH1 (r.comp S.subtype) M) ∧
          FiniteDimensional k (groupCohomology.continuousH2 (r.comp S.subtype) M))
    (HD2 : ∀ (B C : Rep.{u} k S) (ψ : B ⟶ C), (∀ m : B, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ),
          FiniteDimensional ℚ F ∧ ∀ s : S, (r.comp S.subtype) s ∈ F.fixingSubgroup → B.ρ s m = m) → FiniteDimensional k B →
        Function.Surjective ψ.hom → Function.Surjective (groupCohomology.continuousH2MapHom (r.comp S.subtype) ψ))
    (S'' : Subgroup S) [S''.Normal]
    (hS'' : ∃ F₀ : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F₀ ∧
      F₀.fixingSubgroup.comap (r.comp S.subtype) ≤ S'')
    (hidx : S''.index = p) (N : Rep.{u} k S)
    (hsm : ∀ n : N, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s : S, (r.comp S.subtype) s ∈ F.fixingSubgroup → N.ρ s n = n) [FiniteDimensional k N] :
    Module.finrank k (Rep.coind S''.subtype (Rep.res S''.subtype N)).ρ.invariants
      + Module.finrank k (groupCohomology.continuousH2 (r.comp S.subtype) (Rep.coind S''.subtype (Rep.res S''.subtype N)))
      + p * Module.finrank k (groupCohomology.continuousH1 (r.comp S.subtype) N)
    = Module.finrank k (groupCohomology.continuousH1 (r.comp S.subtype) (Rep.coind S''.subtype (Rep.res S''.subtype N)))
      + p * Module.finrank k N.ρ.invariants
      + p * Module.finrank k (groupCohomology.continuousH2 (r.comp S.subtype) N) := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_finrank_euler_coind_res_index_eq_mul.solution
