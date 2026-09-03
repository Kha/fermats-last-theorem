import Definitions.Def_GaloisRep_Flat
import P2M.Util
import P2M.Sol.S_FinFlatHopf_exists_subgroup_inertia_trivial_quotient_cyclotomic
attribute [-instance] MonoidAlgebra.instModuleFiniteOfCartier CartierDual.instCoalgebra CartierDual.instModuleFinite CartierDual.instBialgebra CartierDual.instFunLike CartierDual.instRing CartierDual.instLinearMapClass CartierDual.instCommRing CartierDual.instIsCocomm MonoidAlgebra.instModuleFreeOfCartier CartierDual.instModuleFree CartierDual.instHopfAlgebra CartierDual.instAlgebra CartierDual.instIsCocommViaBialgebra CartierDual.instModuleFreeViaBialgebra CartierDual.instModuleFiniteViaBialgebra AlgebraicClosure.Rat.isGalois
attribute [-simp] CartierDual.toDual_ofDual CartierDual.algebraMap_apply CartierDual.antipode_apply CartierDual.one_apply CartierDual.toDual_apply CartierDual.ofDual_toDual CartierDual.ofDual_apply CartierDual.counit_apply CartierDual.map_apply CartierDual.congr_apply CartierDual.congr_symm_apply CartierDual.pairing_apply CartierDual.mapAlgHom_apply CartierDual.mapLinear_apply

theorem FinFlatHopf.exists_subgroup_inertia_trivial_quotient_cyclotomic (p : ℕ) [Fact p.Prime]
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime p)
    (H : Type) [CommRing H] [HopfAlgebra (GaloisRep.ratLocalizedAt p) H]
    [Module.Finite (GaloisRep.ratLocalizedAt p) H] [Module.Flat (GaloisRep.ratLocalizedAt p) H]
    [Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt p) H]
    {M : Type} [AddCommGroup M] [DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) M]
    (e : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) ≃ M)
    (he_add : ∀ f g, e (f * g) = e f + e g)
    (he_act : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      (f g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)),
      (∀ x : H, g x = σ (f x)) → e g = σ • (e f))
    (R : Type) [CommRing R] [IsLocalRing R] [Module R M]
    (hR : Nat.card (IsLocalRing.ResidueField R) = p)
    (u : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → Rˣ)
    (hu : ∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ m : M, σ • m = (u σ : R) • m) :
    ∃ T : AddSubgroup M,
      (∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ t ∈ T, σ • t ∈ T) ∧
      (∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ m : M, σ • m - m ∈ T) ∧
      ∀ (n a : ℕ) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ),
        σ ∈ P.inertiaSubgroupIn ℚ →
        (∀ μ : AlgebraicClosure ℚ, μ ^ p ^ n = 1 → σ μ = μ ^ a) →
        (∀ t ∈ T, p ^ n • t = 0) → ∀ t ∈ T, σ • t = a • t := by p2m_exact_reverting @_root_.P2MW.S_FinFlatHopf_exists_subgroup_inertia_trivial_quotient_cyclotomic.solution
