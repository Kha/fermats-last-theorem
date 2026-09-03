import Mathlib
import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_GroupCohomology_RelationModule
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import P2M.Util
import P2M.Sol.S_Rep_exists_hom_ind_injective_exact_of_forall_rho_eq

set_option autoImplicit false
open CategoryTheory NumberField IsDedekindDomain M4aHerbrand ExtCitation

theorem Rep.exists_hom_ind_injective_exact_of_forall_rho_eq
    {G : Type} [Group G] [Fintype G] (N : Subgroup G) [N.Normal] (B : Rep ℤ G) [Fintype B] (p : ℕ) (hB : ∀ b : B, p • b = 0)
    (hN : ∀ g ∈ N, ∀ b : B, B.ρ g b = b) :
    ∃ (ι : B ⟶ (Rep.indFunctor ℤ N.subtype).obj (Rep.res N.subtype B)) (B₁ : Rep ℤ G) (_ : Fintype B₁)
      (ρ : (Rep.indFunctor ℤ N.subtype).obj (Rep.res N.subtype B) ⟶ B₁),
      Function.Injective ι.hom ∧ Function.Exact ι.hom ρ.hom ∧ Function.Surjective ρ.hom ∧
      (∀ b : B₁, p • b = 0) ∧ (∀ g ∈ N, ∀ b : B₁, B₁.ρ g b = b) ∧
      (∀ g ∈ N, ∀ x : (Rep.indFunctor ℤ N.subtype).obj (Rep.res N.subtype B), ((Rep.indFunctor ℤ N.subtype).obj (Rep.res N.subtype B)).ρ g x = x) := by p2m_exact_reverting @_root_.P2MW.S_Rep_exists_hom_ind_injective_exact_of_forall_rho_eq.solution
