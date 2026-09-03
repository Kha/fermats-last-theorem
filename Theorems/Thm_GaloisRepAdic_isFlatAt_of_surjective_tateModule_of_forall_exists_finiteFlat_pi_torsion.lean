import Mathlib
import Definitions.Def_GaloisRep_Adic
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_EllipticCurve_TateModule
import P2M.Util
import P2M.Sol.S_GaloisRepAdic_isFlatAt_of_surjective_tateModule_of_forall_exists_finiteFlat_pi_torsion
attribute [-instance] instIsScalarTowerTensorProduct_definitions
attribute [-simp] closureCounit_apply genericFibreAlgHom_tmul tensorInclusion_closureComul coe_closureAntipode_apply tensorToGenericFibre_tmul tensorInclusion_tmul mem_flatClosure_iff

set_option autoImplicit false
open scoped TensorProduct

theorem GaloisRepAdic.isFlatAt_of_surjective_tateModule_of_forall_exists_finiteFlat_pi_torsion
    (p : ℕ) [Fact p.Prime]
    {J : Type} [AddCommGroup J]
    [DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) J]
    [Module.Finite ℤ_[p] (TateModule p J)]

    (hJ : ∀ n b : ℕ,
      ∃ (G : Type) (_ : CommRing G) (_ : HopfAlgebra (GaloisRep.ratLocalizedAt p) G),
        Module.Finite (GaloisRep.ratLocalizedAt p) G ∧ Module.Flat (GaloisRep.ratLocalizedAt p) G ∧
        Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt p) G ∧
        ∃ e : WithConv (G →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) ≃
            (Fin b → ↥(Submodule.torsionBy ℤ J ((p ^ n : ℕ) : ℤ)).toAddSubgroup),
          (∀ f g, e (f * g) = e f + e g) ∧
          ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
            (f g : WithConv (G →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)),
            (∀ x : G, g x = σ (f x)) →
              ∀ i : Fin b,
                ((e g i : ↥(Submodule.torsionBy ℤ J ((p ^ n : ℕ) : ℤ)).toAddSubgroup) : J) =
                  σ • ((e f i : ↥(Submodule.torsionBy ℤ J ((p ^ n : ℕ) : ℤ)).toAddSubgroup) : J))

    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (IsLocalRing.ResidueField O)] [CharZero O] [Algebra ℤ_[p] O]
    (hpO : (p : O) ∈ IsLocalRing.maximalIdeal O)
    (K : Type) [Field K] [Algebra O K] [IsFractionRing O K] [Algebra ℤ_[p] K]
    [IsScalarTower ℤ_[p] O K]

    (ρ : GaloisRepAdic O)
    (π : K ⊗[ℤ_[p]] TateModule p J →ₗ[K] K ⊗[O] ρ.V) (hπ : Function.Surjective π)
    (hπeq : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : K ⊗[ℤ_[p]] TateModule p J),
      π ((TateModule.rep p J (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ).baseChange K x) =
        (ρ.ρ σ).baseChange K (π x)) :
    ρ.IsFlatAt p := by p2m_exact_reverting @_root_.P2MW.S_GaloisRepAdic_isFlatAt_of_surjective_tateModule_of_forall_exists_finiteFlat_pi_torsion.solution
