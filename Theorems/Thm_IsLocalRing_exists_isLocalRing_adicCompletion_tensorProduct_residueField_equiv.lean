import Mathlib
import P2M.Util
import P2M.Sol.S_IsLocalRing_exists_isLocalRing_adicCompletion_tensorProduct_residueField_equiv

set_option autoImplicit false

universe u v

open IsLocalRing in
open scoped TensorProduct in

theorem IsLocalRing.exists_isLocalRing_adicCompletion_tensorProduct_residueField_equiv
    {O : Type u} {C : Type v} [CommRing O] [IsNoetherianRing O] [IsLocalRing O]
    [CommRing C] [IsNoetherianRing C] [IsLocalRing C]
    [Algebra O C] [Module.Finite O C] [IsLocalHom (algebraMap O C)] :
    ∃ (_ : IsLocalRing ((AdicCompletion (maximalIdeal O) O) ⊗[O] C))
      (_ : IsLocalHom (algebraMap (AdicCompletion (maximalIdeal O) O) ((AdicCompletion (maximalIdeal O) O) ⊗[O] C)))
      (e : ResidueField C ≃+* ResidueField ((AdicCompletion (maximalIdeal O) O) ⊗[O] C)),
      IsAdicComplete (maximalIdeal ((AdicCompletion (maximalIdeal O) O) ⊗[O] C))
        ((AdicCompletion (maximalIdeal O) O) ⊗[O] C) ∧
      (IsDomain (AdicCompletion (maximalIdeal C) C) → IsDomain ((AdicCompletion (maximalIdeal O) O) ⊗[O] C)) ∧
      (FaithfulSMul O C → FaithfulSMul (AdicCompletion (maximalIdeal O) O) ((AdicCompletion (maximalIdeal O) O) ⊗[O] C)) ∧
      ∀ c : C, e (residue C c) = residue ((AdicCompletion (maximalIdeal O) O) ⊗[O] C) (1 ⊗ₜ[O] c) := by p2m_exact_reverting @_root_.P2MW.S_IsLocalRing_exists_isLocalRing_adicCompletion_tensorProduct_residueField_equiv.solution
