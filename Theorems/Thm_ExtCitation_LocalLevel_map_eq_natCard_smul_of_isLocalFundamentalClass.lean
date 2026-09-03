import Mathlib
import Definitions.Def_ExtCitation_LocalLevel_FundamentalClass
import P2M.Util
import P2M.Sol.S_ExtCitation_LocalLevel_map_eq_natCard_smul_of_isLocalFundamentalClass

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory groupCohomology ExtCitation.LocalLevel

theorem ExtCitation.LocalLevel.map_eq_natCard_smul_of_isLocalFundamentalClass (q : ℕ) [Fact q.Prime]
    (L' : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] L']
    (G' : Type) [Group G'] [Finite G'] [MulSemiringAction G' L'] [FaithfulSMul G' L']
    (hG' : ∀ (g : G') (x : ℚ_[q]), g • algebraMap ℚ_[q] L' x = algebraMap ℚ_[q] L' x)
    [MulDistribMulAction G' (↥L')ˣ]
    (hcompat' : ∀ (g : G') (u : (↥L')ˣ), ((g • u : (↥L')ˣ) : L') = g • (u : L'))
    (hsolv : Group.IsSolvable G')
    (K : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] K] (hK' : IsBase q L' G' K)
    (L : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] L] (hLL' : L ≤ L')
    (G : Type) [Group G] [Finite G] [MulSemiringAction G L] [FaithfulSMul G L]
    [MulDistribMulAction G (↥L)ˣ]
    (hcompat : ∀ (g : G) (u : (↥L)ˣ), ((g • u : (↥L)ˣ) : L) = g • (u : L))
    (N : Subgroup G') [N.Normal] (e : G ≃* G' ⧸ N)
    (hL : ∀ x : L', (x : PadicAlgCl q) ∈ L ↔ ∀ n ∈ N, n • x = x)
    (he : ∀ (g : G) (h : G'), (QuotientGroup.mk h : G' ⧸ N) = e g →
      ∀ x : L, ((g • x : L) : PadicAlgCl q) = ((h • (⟨(x : PadicAlgCl q), hLL' x.2⟩ : L') : L') : PadicAlgCl q))
    (u : groupCohomology.H2 (Rep.ofMulDistribMulAction G (↥L)ˣ)) (hu : IsLocalFundamentalClass q L G K u)
    (u' : groupCohomology.H2 (Rep.ofMulDistribMulAction G' (↥L')ˣ)) (hu' : IsLocalFundamentalClass q L' G' K u')
    (ι : Rep.res (e.symm.toMonoidHom.comp (QuotientGroup.mk' N)) (Rep.ofMulDistribMulAction G (↥L)ˣ) ⟶ Rep.ofMulDistribMulAction G' (↥L')ˣ)
    (hι : ∀ v : (↥L)ˣ, (((Additive.toMul (ι.hom (Additive.ofMul v)) : (↥L')ˣ) : L') : PadicAlgCl q) = ((v : L) : PadicAlgCl q)) :
    (groupCohomology.map (e.symm.toMonoidHom.comp (QuotientGroup.mk' N)) ι 2).hom u = Nat.card N • u' := by p2m_exact_reverting @_root_.P2MW.S_ExtCitation_LocalLevel_map_eq_natCard_smul_of_isLocalFundamentalClass.solution
