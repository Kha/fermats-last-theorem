import Mathlib
import Definitions.Def_GroupCohomology_ContinuousH2
import Definitions.Def_GroupCohomology_LevelSubgroup
import P2M.Util
import P2M.Sol.S_Rep_exists_devissage_of_not_simple

set_option autoImplicit false

universe u

open CategoryTheory
theorem Rep.exists_devissage_of_not_simple {k G : Type u} [Field k] [Group G]
    (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (N : Rep.{u} k G)
    (hsm : ∀ n : N, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s : G, r s ∈ F.fixingSubgroup → N.ρ s n = n)
    [FiniteDimensional k N]
    (h : ¬ ∀ W : Submodule k N, (∀ (s : G) (v : N), v ∈ W → N.ρ s v ∈ W) → W = ⊥ ∨ W = ⊤) :
    ∃ (A C : Rep.{u} k G) (φ : A ⟶ N) (ψ : N ⟶ C),
      (∀ n : A, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
          ∀ s : G, r s ∈ F.fixingSubgroup → A.ρ s n = n) ∧
      (∀ n : C, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
          ∀ s : G, r s ∈ F.fixingSubgroup → C.ρ s n = n) ∧
      FiniteDimensional k A ∧ FiniteDimensional k C ∧
      Function.Injective φ.hom ∧ Function.Surjective ψ.hom ∧ (∀ b : N, ψ.hom b = 0 ↔ ∃ a : A, φ.hom a = b) ∧
      Module.finrank k A < Module.finrank k N ∧ Module.finrank k C < Module.finrank k N ∧
      Module.finrank k A + Module.finrank k C = Module.finrank k N ∧
      Nat.card (MonoidHom.mrange A.ρ) ≤ Nat.card (MonoidHom.mrange N.ρ) ∧
      Nat.card (MonoidHom.mrange C.ρ) ≤ Nat.card (MonoidHom.mrange N.ρ) := by p2m_exact_reverting @_root_.P2MW.S_Rep_exists_devissage_of_not_simple.solution
