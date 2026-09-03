import Mathlib
import Definitions.Def_GaloisRep_StrictOrdinary
import P2M.Util
import P2M.Sol.S_GaloisRepAdic_isStrictOrdinaryAt_of_detIsCyclotomic_of_forall_quotientScalar_sq_eq_one

set_option autoImplicit false
theorem GaloisRepAdic.isStrictOrdinaryAt_of_detIsCyclotomic_of_forall_quotientScalar_sq_eq_one
    {A : Type} [CommRing A] [IsLocalRing A] (ρ : GaloisRepAdic A) (p : ℕ)
    (hdet : ρ.DetIsCyclotomic p)
    (h : ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime p →
      ∃ L : Submodule A ρ.V,
        (∃ b : Module.Basis (Fin 2) A ρ.V, L = A ∙ b 0) ∧
        (∀ σ ∈ P.decompositionSubgroup ℚ, ∀ v ∈ L, ρ.ρ σ v ∈ L) ∧
        (∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ v : ρ.V, ρ.ρ σ v - v ∈ L) ∧
        (∀ σ ∈ P.decompositionSubgroup ℚ, ∀ z : A,
          (∀ v : ρ.V, ρ.ρ σ v - z • v ∈ L) → z * z = 1)) :
    ρ.IsStrictOrdinaryAt p := by p2m_exact_reverting @_root_.P2MW.S_GaloisRepAdic_isStrictOrdinaryAt_of_detIsCyclotomic_of_forall_quotientScalar_sq_eq_one.solution
