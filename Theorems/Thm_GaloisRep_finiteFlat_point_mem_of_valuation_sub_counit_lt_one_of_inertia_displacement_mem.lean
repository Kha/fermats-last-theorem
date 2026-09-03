import Definitions.Def_GaloisRep_Flat
import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_GaloisRep_finiteFlat_point_mem_of_valuation_sub_counit_lt_one_of_inertia_displacement_mem
attribute [-instance] instIsScalarTowerTensorProduct_definitions AlgebraicClosure.Rat.isGalois
attribute [-simp] closureCounit_apply genericFibreAlgHom_tmul tensorInclusion_closureComul coe_closureAntipode_apply tensorToGenericFibre_tmul tensorInclusion_tmul mem_flatClosure_iff

theorem GaloisRep.finiteFlat_point_mem_of_valuation_sub_counit_lt_one_of_inertia_displacement_mem
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
    (W : AddSubgroup J)
    (hcos : ∀ σ ∈ Aq.inertiaSubgroupIn ℚ, ∀ x ∈ M, σ • x - x ∈ W) :
    ∀ f : WithConv (H →ₐ[GaloisRep.ratLocalizedAt q] AlgebraicClosure ℚ),
      (∀ h : H, Aq.valuation (f h
        - algebraMap (GaloisRep.ratLocalizedAt q) (AlgebraicClosure ℚ) (Coalgebra.counit h)) < 1) →
      ((e f : ↥M) : J) ∈ W := by p2m_exact_reverting @_root_.P2MW.S_GaloisRep_finiteFlat_point_mem_of_valuation_sub_counit_lt_one_of_inertia_displacement_mem.solution
