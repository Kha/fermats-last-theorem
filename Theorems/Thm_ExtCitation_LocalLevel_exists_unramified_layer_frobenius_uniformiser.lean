import Mathlib
import Definitions.Def_ExtCitation_LocalLevelResidues
import Definitions.Def_GroupCohomology_CyclicCarry
import P2M.Util
import P2M.Sol.S_ExtCitation_LocalLevel_exists_unramified_layer_frobenius_uniformiser

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory groupCohomology ExtCitation.LocalLevel

theorem ExtCitation.LocalLevel.exists_unramified_layer_frobenius_uniformiser (q : ℕ) [Fact q.Prime]
    (K : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] K] (n : ℕ) (hn : 0 < n) :
    ∃ (Kn : IntermediateField ℚ_[q] (PadicAlgCl q)) (_ : FiniteDimensional ℚ_[q] Kn) (_ : K ≤ Kn)
      (Γ : Type) (_ : Group Γ) (_ : Finite Γ) (_ : MulSemiringAction Γ Kn) (_ : FaithfulSMul Γ Kn)
      (_ : MulDistribMulAction Γ (↥Kn)ˣ) (φ : Γ) (π : (↥Kn)ˣ),
      (∀ (g : Γ) (x : ℚ_[q]), g • algebraMap ℚ_[q] Kn x = algebraMap ℚ_[q] Kn x) ∧
      (∀ (g : Γ) (u : (↥Kn)ˣ), ((g • u : (↥Kn)ˣ) : Kn) = g • (u : Kn)) ∧
      (∀ x : Kn, (x : PadicAlgCl q) ∈ K ↔ ∀ g : Γ, g • x = x) ∧
      Nat.card Γ = n ∧ (∀ g : Γ, g ∈ Subgroup.zpowers φ) ∧
      (∀ x : Kn, ‖(x : PadicAlgCl q)‖ ≤ 1 →
        ‖((φ • x : Kn) : PadicAlgCl q) - (x : PadicAlgCl q) ^ Nat.card (IsLocalRing.ResidueField (Rw q K))‖ < 1) ∧
      (∀ g : Γ, g • π = π) ∧ ((π : Kn) : PadicAlgCl q) ∈ K ∧ ‖((π : Kn) : PadicAlgCl q)‖ < 1 ∧
      (∀ y : Kn, ‖(y : PadicAlgCl q)‖ < 1 → ‖(y : PadicAlgCl q)‖ ≤ ‖((π : Kn) : PadicAlgCl q)‖) := by p2m_exact_reverting @_root_.P2MW.S_ExtCitation_LocalLevel_exists_unramified_layer_frobenius_uniformiser.solution
