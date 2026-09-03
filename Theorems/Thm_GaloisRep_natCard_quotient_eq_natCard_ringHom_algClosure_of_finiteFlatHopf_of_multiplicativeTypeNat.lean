import Definitions.Def_GaloisRep_Flat
import Definitions.Def_ModularCurve_MultiplicativeType
import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_GaloisRep_natCard_quotient_eq_natCard_ringHom_algClosure_of_finiteFlatHopf_of_multiplicativeTypeNat
attribute [-instance] instIsScalarTowerTensorProduct_definitions AlgebraicClosure.Rat.isGalois
attribute [-simp] closureCounit_apply genericFibreAlgHom_tmul tensorInclusion_closureComul coe_closureAntipode_apply tensorToGenericFibre_tmul tensorInclusion_tmul mem_flatClosure_iff

theorem GaloisRep.natCard_quotient_eq_natCard_ringHom_algClosure_of_finiteFlatHopf_of_multiplicativeTypeNat
    (q : ℕ) [Fact q.Prime] (hq2 : q ≠ 2)
    (H : Type) [CommRing H] [HopfAlgebra (GaloisRep.ratLocalizedAt q) H]
    [Module.Finite (GaloisRep.ratLocalizedAt q) H] [Module.Flat (GaloisRep.ratLocalizedAt q) H]
    [Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt q) H]
    {J : Type} [AddCommGroup J]
    [DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) J]
    (M : AddSubgroup J)
    (e : WithConv (H →ₐ[GaloisRep.ratLocalizedAt q] AlgebraicClosure ℚ) ≃ ↥M)
    (he_add : ∀ f g, e (f * g) = e f + e g)
    (he_act : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) f g,
      (∀ x : H, g x = σ (f x)) → ((e g : ↥M) : J) = σ • ((e f : ↥M) : J))
    (Aq : ValuationSubring (AlgebraicClosure ℚ)) (hAq : Aq.LiesOverPrime q)
    (m : ℕ) (n : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → ℕ)
    (hn : ∀ σ, ∀ ζ : AlgebraicClosure ℚ, ζ ^ (q ^ m) = 1 → σ ζ = ζ ^ n σ)
    (htors : ∀ x : ↥M, q ^ m • x = 0)
    (W : AddSubgroup J) (hWM : W ≤ M)
    (hμ : ModularCurve.MultiplicativeTypeNat (Aq.inertiaSubgroupIn ℚ) n W)
    (hcos : ∀ σ ∈ Aq.inertiaSubgroupIn ℚ, ∀ x ∈ M, σ • x - x ∈ W) :
    Nat.card (↥M ⧸ W.addSubgroupOf M) = Nat.card (H →+* AlgebraicClosure (ZMod q)) := by p2m_exact_reverting @_root_.P2MW.S_GaloisRep_natCard_quotient_eq_natCard_ringHom_algClosure_of_finiteFlatHopf_of_multiplicativeTypeNat.solution
