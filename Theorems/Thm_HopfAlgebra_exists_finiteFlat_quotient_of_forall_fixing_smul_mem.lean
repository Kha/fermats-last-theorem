import Definitions.Def_GaloisRep_Flat
import P2M.Util
import P2M.Sol.S_HopfAlgebra_exists_finiteFlat_quotient_of_forall_fixing_smul_mem
attribute [-instance] instIsScalarTowerTensorProduct_definitions AlgebraicClosure.Rat.isGalois
attribute [-simp] closureCounit_apply genericFibreAlgHom_tmul tensorInclusion_closureComul coe_closureAntipode_apply tensorToGenericFibre_tmul tensorInclusion_tmul mem_flatClosure_iff

theorem HopfAlgebra.exists_finiteFlat_quotient_of_forall_fixing_smul_mem
    (O : Subring (AlgebraicClosure ℚ)) [IsPrincipalIdealRing ↥O]
    (G : Type) [CommRing G] [HopfAlgebra ↥O G]
    [Module.Finite ↥O G] [Module.Flat ↥O G] [Coalgebra.IsCocomm ↥O G]
    {J : Type} [AddCommGroup J]
    [DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) J]
    (M : AddSubgroup J)
    (e : WithConv (G →ₐ[↥O] AlgebraicClosure ℚ) ≃ ↥M)
    (he_add : ∀ f g, e (f * g) = e f + e g)
    (he_act : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, (∀ x ∈ O, σ x = x) →
      ∀ f g : WithConv (G →ₐ[↥O] AlgebraicClosure ℚ),
        (∀ x : G, g x = σ (f x)) → ((e g : ↥M) : J) = σ • ((e f : ↥M) : J))
    (D : AddSubgroup J)
    (hD : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, (∀ x ∈ O, σ x = x) →
      ∀ y ∈ M, y ∈ D → σ • y ∈ D) :
    ∃ (H' : Type) (_ : CommRing H') (_ : HopfAlgebra ↥O H'),
      Module.Finite ↥O H' ∧ Module.Flat ↥O H' ∧ Coalgebra.IsCocomm ↥O H' ∧
      ∃ (ι : H' →ₐc[↥O] G)
        (e' : WithConv (H' →ₐ[↥O] AlgebraicClosure ℚ) ≃ ↥M ⧸ D.addSubgroupOf M),
        (∀ x y, e' (x * y) = e' x + e' y) ∧
        ∀ φ : WithConv (G →ₐ[↥O] AlgebraicClosure ℚ),
          e' (WithConv.toConv ((WithConv.ofConv φ).comp (ι : H' →ₐ[↥O] G)))
            = QuotientAddGroup.mk (e φ) := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_exists_finiteFlat_quotient_of_forall_fixing_smul_mem.solution
