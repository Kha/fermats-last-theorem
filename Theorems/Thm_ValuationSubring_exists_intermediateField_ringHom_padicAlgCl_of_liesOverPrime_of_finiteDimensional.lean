import Mathlib
import Definitions.Def_PadicAlgCl_RingOfIntegers
import Definitions.Def_GaloisRep_CompletionBridge
import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_ValuationSubring_exists_intermediateField_ringHom_padicAlgCl_of_liesOverPrime_of_finiteDimensional

set_option autoImplicit false

theorem ValuationSubring.exists_intermediateField_ringHom_padicAlgCl_of_liesOverPrime_of_finiteDimensional
    (p : ℕ) [Fact p.Prime]
    {O : Type} [CommRing O] [Algebra O (AlgebraicClosure ℚ)]
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime p)
    (hOP : ∀ x : O, algebraMap O (AlgebraicClosure ℚ) x ∈ P)
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ F]
    (hOF : ∀ x : O, algebraMap O (AlgebraicClosure ℚ) x ∈ F) :
    ∃ (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (_ : FiniteDimensional ℚ_[p] K)
      (ι : AlgebraicClosure ℚ →+* PadicAlgCl p) (φ : O →+* PadicAlgCl.ringOfIntegers p K),
      (∀ x : O, ((φ x : PadicAlgCl.ringOfIntegers p K) : PadicAlgCl p) = ι (algebraMap O (AlgebraicClosure ℚ) x)) ∧
      (∀ t : AlgebraicClosure ℚ, P.valuation t < 1 ↔ ‖ι t‖ < 1) ∧
      (∀ t : AlgebraicClosure ℚ, t ∈ P ↔ ‖ι t‖ ≤ 1) ∧
      (∀ (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (τl : PadicAlgCl p ≃ₐ[PadicAlgCl.ringOfIntegers p K] PadicAlgCl p),
        (∀ s : PadicAlgCl p, τl s = σ s) → σ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p] →
        ∃ (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (τ' : AlgebraicClosure ℚ ≃ₐ[O] AlgebraicClosure ℚ),
          (∀ t : AlgebraicClosure ℚ, τ' t = τ t) ∧ τ ∈ P.inertiaSubgroupIn ℚ ∧ ∀ t : AlgebraicClosure ℚ, ι (τ' t) = τl (ι t)) := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_exists_intermediateField_ringHom_padicAlgCl_of_liesOverPrime_of_finiteDimensional.solution
