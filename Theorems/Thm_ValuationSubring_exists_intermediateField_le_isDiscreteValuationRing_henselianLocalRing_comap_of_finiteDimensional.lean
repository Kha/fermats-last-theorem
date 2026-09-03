import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_ValuationSubring_exists_intermediateField_le_isDiscreteValuationRing_henselianLocalRing_comap_of_finiteDimensional

set_option autoImplicit false

universe u

theorem ValuationSubring.exists_intermediateField_le_isDiscreteValuationRing_henselianLocalRing_comap_of_finiteDimensional
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {K : Type u} [Field K] [Algebra R K] [IsFractionRing R K]
    {Ω : Type u} [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    (A : ValuationSubring Ω) (hA : ∀ r : R, algebraMap K Ω (algebraMap R K r) ∈ A) (hAtop : A ≠ ⊤)
    (K' : IntermediateField K Ω) [FiniteDimensional K ↥K'] :
    ∃ Kh : IntermediateField K Ω, K' ≤ Kh ∧
      (∀ σ : Ω ≃ₐ[K] Ω, σ ∈ A.decompositionSubgroup K → (∀ x : Ω, x ∈ K' → σ x = x) →
        ∀ x : Ω, x ∈ Kh → σ x = x) ∧
      IsDiscreteValuationRing ↥(A.comap (algebraMap ↥Kh Ω)) ∧
      HenselianLocalRing ↥(A.comap (algebraMap ↥Kh Ω)) := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_exists_intermediateField_le_isDiscreteValuationRing_henselianLocalRing_comap_of_finiteDimensional.solution
