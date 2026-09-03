import Mathlib
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_GaloisRep_LocalConditions
import P2M.Util
import P2M.Sol.S_GaloisRepAdic_isFlatAt_of_ordinary_of_unitKummer_decomposition
attribute [-instance] instIsScalarTowerTensorProduct_definitions
attribute [-simp] closureCounit_apply genericFibreAlgHom_tmul tensorInclusion_closureComul coe_closureAntipode_apply tensorToGenericFibre_tmul tensorInclusion_tmul mem_flatClosure_iff

set_option autoImplicit false
theorem GaloisRepAdic.isFlatAt_of_ordinary_of_unitKummer_decomposition
    {A : Type} [CommRing A] [IsLocalRing A] [Finite A] (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (ρ : GaloisRepAdic A) (hdet : ρ.DetIsCyclotomic p)
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime p)
    (b : Module.Basis (Fin 2) A ρ.V)
    (hLD : ∀ σ ∈ P.decompositionSubgroup ℚ, ρ.ρ σ (b 0) ∈ A ∙ b 0)
    (hLI : ∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ v : ρ.V, ρ.ρ σ v - v ∈ A ∙ b 0)
    (N : ℕ) (hN : (p : A) ^ N = 0)
    (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ (p ^ N))
    {t : ℕ} (u β : Fin t → AlgebraicClosure ℚ) (a : Fin t → A)
    (hu : ∀ i, P.valuation (u i) = 1) (huI : ∀ i, ∀ σ ∈ P.inertiaSubgroupIn ℚ, σ (u i) = u i)
    (hβ : ∀ i, β i ^ p ^ N = u i)
    (hdec : ∀ τ ∈ P.inertiaSubgroupIn ℚ, (∀ ξ : AlgebraicClosure ℚ, ξ ^ p ^ N = 1 → τ ξ = ξ) →
      ∀ k : Fin t → ℕ, (∀ i, τ (β i) = ζ ^ (k i) * β i) →
        ρ.ρ τ (b 1) - b 1 = (∑ i, (k i) • a i) • b 0) :
    ρ.IsFlatAt p := by p2m_exact_reverting @_root_.P2MW.S_GaloisRepAdic_isFlatAt_of_ordinary_of_unitKummer_decomposition.solution
