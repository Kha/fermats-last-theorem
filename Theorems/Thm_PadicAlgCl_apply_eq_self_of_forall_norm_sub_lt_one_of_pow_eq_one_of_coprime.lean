import Mathlib
import Definitions.Def_PadicAlgCl_RingOfIntegers
import Definitions.Def_PadicComplex_GaloisAction
import Definitions.Def_GaloisRep_CompletionBridge
import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_PadicAlgCl_apply_eq_self_of_forall_norm_sub_lt_one_of_pow_eq_one_of_coprime

set_option autoImplicit false

open scoped TensorProduct
theorem PadicAlgCl.apply_eq_self_of_forall_norm_sub_lt_one_of_pow_eq_one_of_coprime
    (p : ℕ) [Fact p.Prime] (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)
    (hσ : ∀ x : PadicAlgCl p, ‖x‖ ≤ 1 → ‖σ x - x‖ < 1)
    {m : ℕ} (hm : Nat.Coprime p m) {ζ : PadicAlgCl p} (hζ : ζ ^ m = 1) :
    σ ζ = ζ := by p2m_exact_reverting @_root_.P2MW.S_PadicAlgCl_apply_eq_self_of_forall_norm_sub_lt_one_of_pow_eq_one_of_coprime.solution
