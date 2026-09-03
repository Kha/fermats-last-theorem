import Mathlib
import Definitions.Def_ExtCitation_LocalLevelResidues
import Definitions.Def_GroupCohomology_CyclicCarry
import P2M.Util
import P2M.Sol.S_ExtCitation_LocalLevel_exists_common_overlayer

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory groupCohomology ExtCitation.LocalLevel

theorem ExtCitation.LocalLevel.exists_common_overlayer (q : ℕ) [Fact q.Prime]
    (K : IntermediateField ℚ_[q] (PadicAlgCl q))
    (L : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] L]
    (G : Type) [Group G] [Finite G] [MulSemiringAction G L] [FaithfulSMul G L]
    (hG : ∀ (g : G) (x : ℚ_[q]), g • algebraMap ℚ_[q] L x = algebraMap ℚ_[q] L x)
    [MulDistribMulAction G (↥L)ˣ]
    (hcompat : ∀ (g : G) (u : (↥L)ˣ), ((g • u : (↥L)ˣ) : L) = g • (u : L))
    (hKL : K ≤ L) (hK : ∀ x : L, (x : PadicAlgCl q) ∈ K ↔ ∀ g : G, g • x = x)
    (L' : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] L']
    (G' : Type) [Group G'] [Finite G'] [MulSemiringAction G' L'] [FaithfulSMul G' L']
    (hG' : ∀ (g : G') (x : ℚ_[q]), g • algebraMap ℚ_[q] L' x = algebraMap ℚ_[q] L' x)
    [MulDistribMulAction G' (↥L')ˣ]
    (hcompat' : ∀ (g : G') (u : (↥L')ˣ), ((g • u : (↥L')ˣ) : L') = g • (u : L'))
    (hKL' : K ≤ L') (hK' : ∀ x : L', (x : PadicAlgCl q) ∈ K ↔ ∀ g : G', g • x = x) :
    ∃ (M : IntermediateField ℚ_[q] (PadicAlgCl q)) (_ : FiniteDimensional ℚ_[q] M) (hLM : L ≤ M) (hL'M : L' ≤ M)
      (H : Type) (_ : Group H) (_ : Finite H) (_ : MulSemiringAction H M) (_ : FaithfulSMul H M)
      (_ : MulDistribMulAction H (↥M)ˣ) (N N' : Subgroup H) (_ : N.Normal) (_ : N'.Normal)
      (e : G ≃* H ⧸ N) (e' : G' ≃* H ⧸ N'),
      (∀ (h : H) (x : ℚ_[q]), h • algebraMap ℚ_[q] M x = algebraMap ℚ_[q] M x) ∧
      (∀ (h : H) (u : (↥M)ˣ), ((h • u : (↥M)ˣ) : M) = h • (u : M)) ∧
      (∀ x : M, (x : PadicAlgCl q) ∈ K ↔ ∀ h : H, h • x = x) ∧
      (∀ x : M, (x : PadicAlgCl q) ∈ L ↔ ∀ h ∈ N, h • x = x) ∧
      (∀ x : M, (x : PadicAlgCl q) ∈ L' ↔ ∀ h ∈ N', h • x = x) ∧
      (∀ (g : G) (h : H), (QuotientGroup.mk h : H ⧸ N) = e g →
        ∀ x : L, ((g • x : L) : PadicAlgCl q) = ((h • (⟨(x : PadicAlgCl q), hLM x.2⟩ : M) : M) : PadicAlgCl q)) ∧
      (∀ (g : G') (h : H), (QuotientGroup.mk h : H ⧸ N') = e' g →
        ∀ x : L', ((g • x : L') : PadicAlgCl q) = ((h • (⟨(x : PadicAlgCl q), hL'M x.2⟩ : M) : M) : PadicAlgCl q)) := by p2m_exact_reverting @_root_.P2MW.S_ExtCitation_LocalLevel_exists_common_overlayer.solution
