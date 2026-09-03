import Mathlib
import Definitions.Def_PadicAlgCl_RingOfIntegers
import Definitions.Def_PadicComplex_GaloisAction
import Definitions.Def_GaloisRep_CompletionBridge
import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_PadicAlgCl_exists_frobeniusLift_forall_eq_pow_mul_inertia_mul_of_finiteDimensional

set_option autoImplicit false

open scoped TensorProduct
theorem PadicAlgCl.exists_frobeniusLift_forall_eq_pow_mul_inertia_mul_of_finiteDimensional
    (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K] :
    ∃ (f : ℕ) (φ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p), 0 < f ∧ φ ∈ K.fixingSubgroup ∧
      (∀ x : PadicAlgCl p, ‖x‖ ≤ 1 → ‖φ x - x ^ (p ^ f)‖ < 1) ∧
      ∀ (M : IntermediateField ℚ_[p] (PadicAlgCl p)), FiniteDimensional ℚ_[p] M →
        ∀ σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p, σ ∈ K.fixingSubgroup →
          ∃ (n : ℕ) (ι δ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p),
            ι ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p] ∧ ι ∈ K.fixingSubgroup ∧
            δ ∈ K.fixingSubgroup ∧ δ ∈ M.fixingSubgroup ∧
            σ = φ ^ n * ι * δ := by p2m_exact_reverting @_root_.P2MW.S_PadicAlgCl_exists_frobeniusLift_forall_eq_pow_mul_inertia_mul_of_finiteDimensional.solution
