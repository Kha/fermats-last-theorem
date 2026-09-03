import Mathlib
import P2M.Util
import P2M.Sol.S_HopfAlgebra_exists_finiteFlat_padicInt_withConv_equiv_subquotient
attribute [-instance] instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy WeierstrassCurve.Affine.Point.instFinite instIsScalarTowerTensorProduct_definitions
attribute [-simp] FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq closureCounit_apply genericFibreAlgHom_tmul tensorInclusion_closureComul coe_closureAntipode_apply tensorToGenericFibre_tmul tensorInclusion_tmul mem_flatClosure_iff

set_option autoImplicit false

theorem HopfAlgebra.exists_finiteFlat_padicInt_withConv_equiv_subquotient
    (p : ℕ) [Fact p.Prime]
    (C : Type) [CommRing C] [HopfAlgebra ℤ_[p] C] [Module.Finite ℤ_[p] C] [Module.Flat ℤ_[p] C]
    [Coalgebra.IsCocomm ℤ_[p] C]
    {P : Type} [AddCommGroup P] [DistribMulAction (AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p]) P]
    (eC : WithConv (C →ₐ[ℤ_[p]] AlgebraicClosure ℚ_[p]) ≃ P)
    (heC_add : ∀ f g, eC (f * g) = eC f + eC g)
    (heC_act : ∀ (σ : (AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p])) (f g : WithConv (C →ₐ[ℤ_[p]] AlgebraicClosure ℚ_[p])),
      (∀ x : C, g x = σ (f x)) → eC g = σ • (eC f))
    (P' : AddSubgroup P) (hP' : ∀ (σ : (AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p])) (x : P), x ∈ P' → σ • x ∈ P')
    {N : Type} [AddCommGroup N] [DistribMulAction (AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p]) N]
    (π : ↥P' →+ N) (hπ : Function.Surjective π)
    (hπ_act : ∀ (σ : (AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p])) (x : ↥P'), π ⟨σ • (x : P), hP' σ x x.2⟩ = σ • π x) :
    ∃ (H : Type) (_ : CommRing H) (_ : HopfAlgebra ℤ_[p] H),
      Module.Finite ℤ_[p] H ∧ Module.Flat ℤ_[p] H ∧ Coalgebra.IsCocomm ℤ_[p] H ∧
      ∃ e : WithConv (H →ₐ[ℤ_[p]] AlgebraicClosure ℚ_[p]) ≃ N,
        (∀ f g, e (f * g) = e f + e g) ∧
        ∀ (σ : (AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p]))
          (f g : WithConv (H →ₐ[ℤ_[p]] AlgebraicClosure ℚ_[p])),
          (∀ x : H, g x = σ (f x)) → e g = σ • (e f) := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_exists_finiteFlat_padicInt_withConv_equiv_subquotient.solution
