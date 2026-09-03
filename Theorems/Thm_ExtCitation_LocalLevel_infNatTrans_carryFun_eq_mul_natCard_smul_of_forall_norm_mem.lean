import Mathlib
import Definitions.Def_ExtCitation_LocalLevel_FundamentalClass
import P2M.Util
import P2M.Sol.S_ExtCitation_LocalLevel_infNatTrans_carryFun_eq_mul_natCard_smul_of_forall_norm_mem
attribute [-simp] IsLocalRing.principalUnits_zero groupCohomology.Cores.Transversal.mk.sizeOf_spec groupCohomology.Cores.Transversal.mk.injEq
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
open CategoryTheory groupCohomology ExtCitation.LocalLevel

theorem ExtCitation.LocalLevel.infNatTrans_carryFun_eq_mul_natCard_smul_of_forall_norm_mem
    (q : ℕ) [Fact q.Prime]
    (M : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] M]
    (H : Type) [Group H] [Finite H] [IsMulCommutative H] [MulSemiringAction H M] [FaithfulSMul H M]
    (hH : ∀ (h : H) (x : ℚ_[q]), h • algebraMap ℚ_[q] M x = algebraMap ℚ_[q] M x)
    [MulDistribMulAction H (↥M)ˣ]
    (hcompat : ∀ (h : H) (b : (↥M)ˣ), ((h • b : (↥M)ˣ) : M) = h • (b : M))
    (K : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] K] (hK : IsBase q M H K)
    (u : groupCohomology.H2 (Rep.ofMulDistribMulAction H (↥M)ˣ)) (hu : IsLocalFundamentalClass q M H K u)

    (Nn : Subgroup H) [Nn.Normal] (φ : H) (π : (↥M)ˣ)
    (hzp : ∀ h : H ⧸ Nn, h ∈ Subgroup.zpowers (QuotientGroup.mk' Nn φ))
    (hfrob : ∀ x : M, (∀ h ∈ Nn, h • x = x) → ‖(x : PadicAlgCl q)‖ ≤ 1 →
      ‖((φ • x : M) : PadicAlgCl q) - (x : PadicAlgCl q) ^ Nat.card (IsLocalRing.ResidueField (Rw q K))‖ < 1)
    (hπH : ∀ h : H, h • π = π) (hπ1 : ‖((π : M) : PadicAlgCl q)‖ < 1)
    (hπmax : ∀ y : M, (∀ h ∈ Nn, h • y = y) → ‖(y : PadicAlgCl q)‖ < 1 → ‖(y : PadicAlgCl q)‖ ≤ ‖((π : M) : PadicAlgCl q)‖)

    (hexp : ∀ h : H, h ^ Nn.index = 1)

    (f : (↥K)ˣ →* H)
    (h1 : ∀ (a : (↥K)ˣ) (k : ℤ), ‖((a : K) : PadicAlgCl q)‖ = ‖((π : M) : PadicAlgCl q)‖ ^ k →
      (QuotientGroup.mk (f a) : H ⧸ Nn) = (QuotientGroup.mk φ : H ⧸ Nn) ^ k)
    (h2 : ∀ (H' : Subgroup H) (a : (↥K)ˣ),
      (∃ b : (↥M)ˣ, (∀ h ∈ H', h • b = b) ∧
        ∏ᶠ c : H ⧸ H', (Quotient.out c) • b = Units.map (IntermediateField.inclusion hK.le).toRingHom.toMonoidHom a) →
      f a ∈ H')

    (H' : Subgroup H) [H'.Normal] (t : H ⧸ H') (ht : ∀ c : H ⧸ H', c ∈ Subgroup.zpowers t) (htfin : IsOfFinOrder t)
    (a : (↥K)ˣ) (m : ℕ) (hm : (QuotientGroup.mk (f a) : H ⧸ H') = t ^ m)
    (hfix : (Additive.ofMul (Units.map (IntermediateField.inclusion hK.le).toRingHom.toMonoidHom a) : Rep.ofMulDistribMulAction H (↥M)ˣ) ∈
      Representation.invariants ((Rep.ofMulDistribMulAction H (↥M)ˣ).ρ.comp H'.subtype))
    (hc : carryFun t ht htfin (A := (Rep.ofMulDistribMulAction H (↥M)ˣ).quotientToInvariants H')
        ⟨Additive.ofMul (Units.map (IntermediateField.inclusion hK.le).toRingHom.toMonoidHom a), hfix⟩ ∈
      cocycles₂ ((Rep.ofMulDistribMulAction H (↥M)ˣ).quotientToInvariants H')) :
    ((infNatTrans ℤ H' 2).app (Rep.ofMulDistribMulAction H (↥M)ˣ)).hom
        ((H2π ((Rep.ofMulDistribMulAction H (↥M)ˣ).quotientToInvariants H')).hom
          ⟨carryFun t ht htfin (A := (Rep.ofMulDistribMulAction H (↥M)ˣ).quotientToInvariants H')
            ⟨Additive.ofMul (Units.map (IntermediateField.inclusion hK.le).toRingHom.toMonoidHom a), hfix⟩, hc⟩) =
      (m * Nat.card H') • u := by p2m_exact_reverting @_root_.P2MW.S_ExtCitation_LocalLevel_infNatTrans_carryFun_eq_mul_natCard_smul_of_forall_norm_mem.solution
