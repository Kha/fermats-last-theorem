import Mathlib
import Definitions.Def_ExtCitation_LocalLevelResidues
import Definitions.Def_GroupCohomology_CyclicCarry
import P2M.Util
import P2M.Sol.S_ExtCitation_LocalLevel_exists_overlayer_unramified_level

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory groupCohomology ExtCitation.LocalLevel

theorem ExtCitation.LocalLevel.exists_overlayer_unramified_level (q : ℕ) [Fact q.Prime]
    (L : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] L]
    (G : Type) [Group G] [Finite G] [MulSemiringAction G L] [FaithfulSMul G L]
    (hG : ∀ (g : G) (x : ℚ_[q]), g • algebraMap ℚ_[q] L x = algebraMap ℚ_[q] L x)
    [MulDistribMulAction G (↥L)ˣ]
    (hcompat : ∀ (g : G) (u : (↥L)ˣ), ((g • u : (↥L)ˣ) : L) = g • (u : L))
    (K : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] K] (hKL : K ≤ L)
    (hK : ∀ x : L, (x : PadicAlgCl q) ∈ K ↔ ∀ g : G, g • x = x) (n : ℕ) (hn : 0 < n) :
    ∃ (M : IntermediateField ℚ_[q] (PadicAlgCl q)) (_ : FiniteDimensional ℚ_[q] M) (hLM : L ≤ M)
      (H : Type) (_ : Group H) (_ : Finite H) (_ : MulSemiringAction H M) (_ : FaithfulSMul H M)
      (_ : MulDistribMulAction H (↥M)ˣ) (NL Nn : Subgroup H) (_ : NL.Normal) (_ : Nn.Normal)
      (e : G ≃* H ⧸ NL) (φ : H) (π : (↥M)ˣ),
      (∀ (h : H) (x : ℚ_[q]), h • algebraMap ℚ_[q] M x = algebraMap ℚ_[q] M x) ∧
      (∀ (h : H) (u : (↥M)ˣ), ((h • u : (↥M)ˣ) : M) = h • (u : M)) ∧
      (∀ x : M, (x : PadicAlgCl q) ∈ K ↔ ∀ h : H, h • x = x) ∧
      (∀ x : M, (x : PadicAlgCl q) ∈ L ↔ ∀ h ∈ NL, h • x = x) ∧
      (∀ (g : G) (h : H), (QuotientGroup.mk h : H ⧸ NL) = e g →
        ∀ x : L, ((g • x : L) : PadicAlgCl q) = ((h • (⟨(x : PadicAlgCl q), hLM x.2⟩ : M) : M) : PadicAlgCl q)) ∧
      Nat.card (H ⧸ Nn) = n ∧ (∀ h : H ⧸ Nn, h ∈ Subgroup.zpowers (QuotientGroup.mk' Nn φ)) ∧
      (∀ x : M, (∀ h ∈ Nn, h • x = x) → ‖(x : PadicAlgCl q)‖ ≤ 1 →
        ‖((φ • x : M) : PadicAlgCl q) - (x : PadicAlgCl q) ^ Nat.card (IsLocalRing.ResidueField (Rw q K))‖ < 1) ∧
      (∀ h : H, h • π = π) ∧ ((π : M) : PadicAlgCl q) ∈ K ∧ ‖((π : M) : PadicAlgCl q)‖ < 1 ∧
      (∀ y : M, (∀ h ∈ Nn, h • y = y) → ‖(y : PadicAlgCl q)‖ < 1 → ‖(y : PadicAlgCl q)‖ ≤ ‖((π : M) : PadicAlgCl q)‖) := by p2m_exact_reverting @_root_.P2MW.S_ExtCitation_LocalLevel_exists_overlayer_unramified_level.solution
