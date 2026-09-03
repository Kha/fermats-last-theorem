import Definitions.Def_GaloisRep_Flat
import Definitions.Def_FLTPrelim_Ramification
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Theorems.Thm_GaloisRep_exists_finset_forall_dvr_finiteFlat_inertia_displacement_quotient_of_finiteFlatHopf
import Theorems.Thm_ValuationSubring_exists_dvr_subring_of_forall_mem_inertiaSubgroupIn
import P2M.Util
namespace P2MW.S_GaloisRep_exists_finiteFlat_inertia_displacement_quotient_of_finiteFlatHopf
attribute [-instance] instIsScalarTowerTensorProduct_definitions AlgebraicClosure.Rat.isGalois
attribute [-simp] closureCounit_apply genericFibreAlgHom_tmul tensorInclusion_closureComul coe_closureAntipode_apply tensorToGenericFibre_tmul tensorInclusion_tmul mem_flatClosure_iff

theorem solution
    (q : ℕ) [Fact q.Prime]
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
    (Aq : ValuationSubring (AlgebraicClosure ℚ)) (hAq : Aq.LiesOverPrime q) :
    ∃ O : Subring (AlgebraicClosure ℚ),
      IsDiscreteValuationRing ↥O ∧ Irreducible ((q : ℕ) : ↥O) ∧
      ∃ (H' : Type) (_ : CommRing H') (_ : HopfAlgebra ↥O H'),
        Module.Finite ↥O H' ∧ Module.Flat ↥O H' ∧ Coalgebra.IsCocomm ↥O H' ∧
        Finite (WithConv (H' →ₐ[↥O] ↥O)) ∧
        ∃ e' : WithConv (H' →ₐ[↥O] ↥O) ≃
            ↥M ⧸ (AddSubgroup.closure
              {y : J | ∃ σ ∈ Aq.inertiaSubgroupIn ℚ, ∃ x ∈ M, y = σ • x - x}).addSubgroupOf M,
          (∀ x y, e' (x * y) = e' x + e' y) ∧
          ∀ φ : WithConv (H →ₐ[GaloisRep.ratLocalizedAt q] AlgebraicClosure ℚ),
            ∃ x : WithConv (H' →ₐ[↥O] ↥O),
              e' x = QuotientAddGroup.mk (e φ) ∧
              ((∀ h : H, Aq.valuation (φ h
                  - algebraMap (GaloisRep.ratLocalizedAt q) (AlgebraicClosure ℚ)
                    (Coalgebra.counit h)) < 1) →
                ∀ h' : H', x h' - algebraMap ↥O ↥O (Coalgebra.counit h') ∈ nonunits ↥O) := by
  obtain ⟨S, hSfix, huniv⟩ :=
    GaloisRep.exists_finset_forall_dvr_finiteFlat_inertia_displacement_quotient_of_finiteFlatHopf
      q H M e he_add he_act Aq hAq
  obtain ⟨O, hSO, hOA, hOrat, hdvr, hirr, hnon⟩ :=
    ValuationSubring.exists_dvr_subring_of_forall_mem_inertiaSubgroupIn q Aq hAq S hSfix
  exact ⟨O, hdvr, hirr, huniv O hSO hOA hOrat hdvr hirr hnon⟩
