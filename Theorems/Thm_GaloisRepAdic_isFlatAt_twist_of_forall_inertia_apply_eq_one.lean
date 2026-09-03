import Definitions.Def_GaloisRep_Flat
import Definitions.Def_GaloisRep_Twist
import P2M.Util
import P2M.Sol.S_GaloisRepAdic_isFlatAt_twist_of_forall_inertia_apply_eq_one
attribute [-instance] instIsScalarTowerTensorProduct_definitions
attribute [-simp] closureCounit_apply genericFibreAlgHom_tmul tensorInclusion_closureComul coe_closureAntipode_apply tensorToGenericFibre_tmul tensorInclusion_tmul mem_flatClosure_iff

set_option autoImplicit false

theorem GaloisRepAdic.isFlatAt_twist_of_forall_inertia_apply_eq_one
    {A : Type} [CommRing A] [IsLocalRing A] (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (ρ : GaloisRepAdic A) (χ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Aˣ)
    (hχ : GaloisCharIsAdicContinuous A χ)
    (hunr : ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime p →
      ∀ σ ∈ P.inertiaSubgroupIn ℚ, χ σ = 1)
    (hflat : ρ.IsFlatAt p) :
    (ρ.twist χ hχ).IsFlatAt p := by p2m_exact_reverting @_root_.P2MW.S_GaloisRepAdic_isFlatAt_twist_of_forall_inertia_apply_eq_one.solution
