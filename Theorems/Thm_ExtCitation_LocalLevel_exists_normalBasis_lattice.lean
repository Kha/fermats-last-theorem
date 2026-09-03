import Mathlib
import Definitions.Def_ExtCitation_LocalLevelResidues
import P2M.Util
import P2M.Sol.S_ExtCitation_LocalLevel_exists_normalBasis_lattice

set_option autoImplicit false
open ExtCitation.LocalLevel
theorem ExtCitation.LocalLevel.exists_normalBasis_lattice (q : ℕ) [Fact q.Prime]
    (L : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] L]
    (G : Type) [Group G] [Finite G] [MulSemiringAction G L] [FaithfulSMul G L]
    (hG : ∀ (g : G) (x : ℚ_[q]), g • algebraMap ℚ_[q] L x = algebraMap ℚ_[q] L x) :
    ∃ (A₀ A : Submodule ℤ_[q] L) (c : ℕ),
      A.FG ∧
      (∀ a ∈ A, a ∈ Rw q L) ∧
      (∀ (g : G) (a : L), a ∈ A → g • a ∈ A) ∧
      (∀ x : G → L, (∀ g, x g ∈ A₀) → (∑ᶠ g, g • x g) ∈ A) ∧
      (∀ a ∈ A, ∃! x : G → L, (∀ g, x g ∈ A₀) ∧ (∑ᶠ g, g • x g) = a) ∧
      (∀ y : L, y ∈ Rw q L → ((q : ℚ_[q]) ^ c) • y ∈ A) := by p2m_exact_reverting @_root_.P2MW.S_ExtCitation_LocalLevel_exists_normalBasis_lattice.solution
