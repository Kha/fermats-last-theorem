import Mathlib
import Definitions.Def_ExtCitation_LocalLevelResidues
import Definitions.Def_GroupCohomology_CyclicCarry
import P2M.Util
import P2M.Sol.S_ExtCitation_LocalLevel_inv_res_inf_eq_index_smul_inv

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory groupCohomology ExtCitation.LocalLevel

theorem ExtCitation.LocalLevel.inv_res_inf_eq_index_smul_inv (q : ℕ) [Fact q.Prime]
    (L : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] L]
    (G : Type) [Group G] [Finite G] [MulSemiringAction G L] [FaithfulSMul G L]
    (hG : ∀ (g : G) (x : ℚ_[q]), g • algebraMap ℚ_[q] L x = algebraMap ℚ_[q] L x)
    [MulDistribMulAction G (↥L)ˣ]
    (hcompat : ∀ (g : G) (u : (↥L)ˣ), ((g • u : (↥L)ˣ) : L) = g • (u : L))
    (K : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] K] (hKL : K ≤ L)
    (hK : ∀ x : L, (x : PadicAlgCl q) ∈ K ↔ ∀ g : G, g • x = x)
    (S : Subgroup G)
    (K' : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] K'] (hK'L : K' ≤ L)
    (hK' : ∀ x : L, (x : PadicAlgCl q) ∈ K' ↔ ∀ s ∈ S, s • x = x)
    (N : Subgroup G) [N.Normal]
    (φ : G) (hφN : ∀ g : G ⧸ N, g ∈ Subgroup.zpowers (QuotientGroup.mk' N φ)) (hfinN : IsOfFinOrder (QuotientGroup.mk' N φ))
    (hφ : ∀ x : L, (∀ n ∈ N, n • x = x) → ‖(x : PadicAlgCl q)‖ ≤ 1 →
      ‖((φ • x : L) : PadicAlgCl q) - (x : PadicAlgCl q) ^ Nat.card (IsLocalRing.ResidueField (Rw q K))‖ < 1)
    (π : (↥L)ˣ) (hπG : ∀ g : G, g • π = π) (hπ1 : ‖((π : L) : PadicAlgCl q)‖ < 1)
    (hπmax : ∀ y : L, (∀ n ∈ N, n • y = y) → ‖(y : PadicAlgCl q)‖ < 1 → ‖(y : PadicAlgCl q)‖ ≤ ‖((π : L) : PadicAlgCl q)‖)
    (ψ : S) (hψN : ∀ g : S ⧸ N.subgroupOf S, g ∈ Subgroup.zpowers (QuotientGroup.mk' (N.subgroupOf S) ψ))
    (hfinψ : IsOfFinOrder (QuotientGroup.mk' (N.subgroupOf S) ψ))
    (hψ : ∀ x : L, (∀ n ∈ N ⊓ S, n • x = x) → ‖(x : PadicAlgCl q)‖ ≤ 1 →
      ‖(((ψ : G) • x : L) : PadicAlgCl q) - (x : PadicAlgCl q) ^ Nat.card (IsLocalRing.ResidueField (Rw q K'))‖ < 1)
    (π' : (↥L)ˣ) (hπ'S : ∀ s ∈ S, s • π' = π') (hπ'1 : ‖((π' : L) : PadicAlgCl q)‖ < 1)
    (hπ'max : ∀ y : L, (∀ n ∈ N ⊓ S, n • y = y) → ‖(y : PadicAlgCl q)‖ < 1 → ‖(y : PadicAlgCl q)‖ ≤ ‖((π' : L) : PadicAlgCl q)‖)
    (inv : groupCohomology.H2 ((Rep.ofMulDistribMulAction G (↥L)ˣ).quotientToInvariants N) ≃+ ZMod (Nat.card (G ⧸ N)))
    (hinv : ∀ (a : (Rep.ofMulDistribMulAction G (↥L)ˣ).quotientToInvariants N) (k : ℤ)
        (hc : carryFun (QuotientGroup.mk' N φ) hφN hfinN a ∈ cocycles₂ ((Rep.ofMulDistribMulAction G (↥L)ˣ).quotientToInvariants N)),
        ‖((Additive.toMul (a.1 : Additive (↥L)ˣ) : (↥L)ˣ) : PadicAlgCl q)‖ = ‖((π : L) : PadicAlgCl q)‖ ^ k →
          inv ((H2π ((Rep.ofMulDistribMulAction G (↥L)ˣ).quotientToInvariants N)).hom
              ⟨carryFun (QuotientGroup.mk' N φ) hφN hfinN a, hc⟩) = (k : ZMod (Nat.card (G ⧸ N))))
    (inv' : groupCohomology.H2 ((Rep.res S.subtype (Rep.ofMulDistribMulAction G (↥L)ˣ)).quotientToInvariants (N.subgroupOf S)) ≃+
        ZMod (Nat.card (S ⧸ N.subgroupOf S)))
    (hinv' : ∀ (a : (Rep.res S.subtype (Rep.ofMulDistribMulAction G (↥L)ˣ)).quotientToInvariants (N.subgroupOf S)) (k : ℤ)
        (hc : carryFun (QuotientGroup.mk' (N.subgroupOf S) ψ) hψN hfinψ a ∈
          cocycles₂ ((Rep.res S.subtype (Rep.ofMulDistribMulAction G (↥L)ˣ)).quotientToInvariants (N.subgroupOf S))),
        ‖((Additive.toMul (a.1 : Additive (↥L)ˣ) : (↥L)ˣ) : PadicAlgCl q)‖ = ‖((π' : L) : PadicAlgCl q)‖ ^ k →
          inv' ((H2π ((Rep.res S.subtype (Rep.ofMulDistribMulAction G (↥L)ˣ)).quotientToInvariants (N.subgroupOf S))).hom
              ⟨carryFun (QuotientGroup.mk' (N.subgroupOf S) ψ) hψN hfinψ a, hc⟩) = (k : ZMod (Nat.card (S ⧸ N.subgroupOf S))))
    (x : groupCohomology.H2 ((Rep.ofMulDistribMulAction G (↥L)ˣ).quotientToInvariants N))
    (y : groupCohomology.H2 ((Rep.res S.subtype (Rep.ofMulDistribMulAction G (↥L)ˣ)).quotientToInvariants (N.subgroupOf S)))
    (hxy : (map S.subtype (𝟙 (Rep.res S.subtype (Rep.ofMulDistribMulAction G (↥L)ˣ))) 2).hom
        (((infNatTrans ℤ N 2).app (Rep.ofMulDistribMulAction G (↥L)ˣ)).hom x) =
      ((infNatTrans ℤ (N.subgroupOf S) 2).app (Rep.res S.subtype (Rep.ofMulDistribMulAction G (↥L)ˣ))).hom y) :
    (((((inv' y).val : ℚ) / (Nat.card (S ⧸ N.subgroupOf S) : ℚ)) : ℚ) : AddCircle (1 : ℚ)) =
      S.index • (((((inv x).val : ℚ) / (Nat.card (G ⧸ N) : ℚ)) : ℚ) : AddCircle (1 : ℚ)) := by p2m_exact_reverting @_root_.P2MW.S_ExtCitation_LocalLevel_inv_res_inf_eq_index_smul_inv.solution
