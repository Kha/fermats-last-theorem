import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_isClopen_preimage_sigmaInj_and_existsUnique_lift_of_hom_sigma

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

theorem AlgebraicGeometry.Scheme.isClopen_preimage_sigmaInj_and_existsUnique_lift_of_hom_sigma
    {σ : Type u} (H : σ → Scheme.{u}) {T : Scheme.{u}} (u : T ⟶ ∐ H) :
    (∀ i, IsClosed ((u ⁻¹ᵁ (Sigma.ι H i).opensRange : T.Opens) : Set T)) ∧
    (∀ i j, i ≠ j → Disjoint (u ⁻¹ᵁ (Sigma.ι H i).opensRange) (u ⁻¹ᵁ (Sigma.ι H j).opensRange)) ∧
    (⨆ i, u ⁻¹ᵁ (Sigma.ι H i).opensRange) = ⊤ ∧
    (∀ i, ∃! v : ((u ⁻¹ᵁ (Sigma.ι H i).opensRange : T.Opens) : Scheme.{u}) ⟶ H i,
      v ≫ Sigma.ι H i = (u ⁻¹ᵁ (Sigma.ι H i).opensRange).ι ≫ u) ∧
    (CompactSpace T → {i : σ | ((u ⁻¹ᵁ (Sigma.ι H i).opensRange : T.Opens) : Set T).Nonempty}.Finite) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_isClopen_preimage_sigmaInj_and_existsUnique_lift_of_hom_sigma.solution
