import Mathlib
import Definitions.Def_PadicAlgCl_RingOfIntegers
import Definitions.Def_PadicComplex_GaloisAction
import Definitions.Def_GaloisRep_CompletionBridge
import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_PadicAlgCl_exists_rootOfUnity_norm_sub_lt_one_and_artinSchreier_and_lang

set_option autoImplicit false

open scoped TensorProduct
theorem PadicAlgCl.exists_rootOfUnity_norm_sub_lt_one_and_artinSchreier_and_lang
    (p : ℕ) [Fact p.Prime] :
    (∀ x : PadicAlgCl p, ‖x‖ ≤ 1 →
      ∃ ζ : PadicAlgCl p, (ζ = 0 ∨ ∃ m : ℕ, Nat.Coprime p m ∧ ζ ^ m = 1) ∧ ‖x - ζ‖ < 1) ∧
    (∀ (q : ℕ), p ∣ q → 1 < q → ∀ c : PadicAlgCl p, ‖c‖ ≤ 1 →
      ∃ y : PadicAlgCl p, (y = 0 ∨ ∃ m : ℕ, Nat.Coprime p m ∧ y ^ m = 1) ∧ ‖y ^ q - y - c‖ < 1) ∧
    (∀ (q : ℕ), p ∣ q → 1 < q → ∀ a : PadicAlgCl p, ‖a‖ = 1 →
      ∃ y : PadicAlgCl p, (∃ m : ℕ, Nat.Coprime p m ∧ y ^ m = 1) ∧ ‖y ^ (q - 1) - a‖ < 1) := by p2m_exact_reverting @_root_.P2MW.S_PadicAlgCl_exists_rootOfUnity_norm_sub_lt_one_and_artinSchreier_and_lang.solution
