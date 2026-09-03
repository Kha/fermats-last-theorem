import Mathlib
import Definitions.Def_GroupCohomology_ContinuousH2
import Definitions.Def_GroupCohomology_LevelSubgroup
import Definitions.Def_GroupCohomology_ContinuousH2Map
import Definitions.Def_GroupCohomology_ContinuousH1
import Definitions.Def_GroupCohomology_Selmer
import P2M.Util
import P2M.Sol.S_groupCohomology_euler_poincare_identity_of_hypotheses

set_option autoImplicit false

universe u

open CategoryTheory
theorem groupCohomology.euler_poincare_identity_of_hypotheses {k G : Type u} [Field k] [Group G] (p : ℕ) [Fact p.Prime] [CharP k p]
    (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (χ : G →* kˣ)
    (IsTame : ∀ S : Subgroup G, Rep.{u} k S → Prop)

    (HFIN : ∀ (S : Subgroup G), (∃ F₀ : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F₀ ∧ F₀.fixingSubgroup.comap r ≤ S) →
      ∀ (N : Rep.{u} k S), (∀ n : N, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
          ∀ s : S, (r.comp S.subtype) s ∈ F.fixingSubgroup → N.ρ s n = n) → FiniteDimensional k N →
        FiniteDimensional k (groupCohomology.continuousH1 (r.comp S.subtype) N) ∧
          FiniteDimensional k (groupCohomology.continuousH2 (r.comp S.subtype) N))

    (HD2 : ∀ (S : Subgroup G), (∃ F₀ : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F₀ ∧ F₀.fixingSubgroup.comap r ≤ S) →
      ∀ (B C : Rep.{u} k S) (ψ : B ⟶ C), (∀ n : B, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
          ∀ s : S, (r.comp S.subtype) s ∈ F.fixingSubgroup → B.ρ s n = n) → FiniteDimensional k B →
        Function.Surjective ψ.hom → Function.Surjective (groupCohomology.continuousH2MapHom (r.comp S.subtype) ψ))

    (HTAME1 : ∀ (S : Subgroup G), (∃ F₀ : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F₀ ∧ F₀.fixingSubgroup.comap r ≤ S) →
      ∀ (N : Rep.{u} k S), (∀ n : N, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
          ∀ s : S, (r.comp S.subtype) s ∈ F.fixingSubgroup → N.ρ s n = n) → FiniteDimensional k N →
        FiniteDimensional k (groupCohomology.continuousH1 (r.comp S.subtype) N) →
        IsTame S N →
        Module.finrank k (groupCohomology.continuousH1 (r.comp S.subtype) N)
          = Module.finrank k N.ρ.invariants + Module.finrank k (N.dualTwist (χ.comp S.subtype)).ρ.invariants
            + S.index * Module.finrank k N)

    (HTAME2 : ∀ (S : Subgroup G), (∃ F₀ : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F₀ ∧ F₀.fixingSubgroup.comap r ≤ S) →
      ∀ (N : Rep.{u} k S), (∀ n : N, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
          ∀ s : S, (r.comp S.subtype) s ∈ F.fixingSubgroup → N.ρ s n = n) → FiniteDimensional k N →
        IsTame S N →
        Module.finrank k (groupCohomology.continuousH2 (r.comp S.subtype) N)
          = Module.finrank k (N.dualTwist (χ.comp S.subtype)).ρ.invariants)

    (HARITH : ∀ (S : Subgroup G), (∃ F₀ : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F₀ ∧ F₀.fixingSubgroup.comap r ≤ S) →
      ∀ (N : Rep.{u} k S), (∀ n : N, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
          ∀ s : S, (r.comp S.subtype) s ∈ F.fixingSubgroup → N.ρ s n = n) → FiniteDimensional k N → Module.finrank k N ≠ 0 →
        (∀ W : Submodule k N, (∀ (s : S) (v : N), v ∈ W → N.ρ s v ∈ W) → W = ⊥ ∨ W = ⊤) →
        IsTame S N ∨
        (∃ (S' : Subgroup G) (hle : S' ≤ S), (∃ F₀ : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F₀ ∧ F₀.fixingSubgroup.comap r ≤ S') ∧ (S'.subgroupOf S).Normal ∧ (S'.subgroupOf S).index = p ∧
            Nat.card (MonoidHom.mrange (N.ρ.comp (Subgroup.inclusion hle)))
              < Nat.card (MonoidHom.mrange N.ρ)))

    (S : Subgroup G) (hS : (∃ F₀ : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F₀ ∧ F₀.fixingSubgroup.comap r ≤ S)) (N : Rep.{u} k S)
    (hsm : (∀ n : N, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
          ∀ s : S, (r.comp S.subtype) s ∈ F.fixingSubgroup → N.ρ s n = n)) [FiniteDimensional k N] :
    Module.finrank k (groupCohomology.continuousH1 (r.comp S.subtype) N)
            = Module.finrank k N.ρ.invariants + Module.finrank k (groupCohomology.continuousH2 (r.comp S.subtype) N)
              + S.index * Module.finrank k N := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_euler_poincare_identity_of_hypotheses.solution
