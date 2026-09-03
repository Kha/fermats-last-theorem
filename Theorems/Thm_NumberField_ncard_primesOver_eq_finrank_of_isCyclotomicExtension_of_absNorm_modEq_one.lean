import Mathlib
import P2M.Util
import P2M.Sol.S_NumberField_ncard_primesOver_eq_finrank_of_isCyclotomicExtension_of_absNorm_modEq_one
attribute [-instance] Deep.NTSupply.instNormalRayClassSubgroup

set_option autoImplicit false

open NumberField

theorem NumberField.ncard_primesOver_eq_finrank_of_isCyclotomicExtension_of_absNorm_modEq_one
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (m : ℕ) [NeZero m] [IsCyclotomicExtension {m} K L]
    (v : Ideal (𝓞 K)) [v.IsMaximal] (hcop : (Ideal.absNorm v).Coprime m)
    (h1 : (Ideal.absNorm v : ZMod m) = 1) :
    (v.primesOver (𝓞 L)).ncard = Module.finrank K L ∧
      ∀ w : Ideal (𝓞 L), w ∈ v.primesOver (𝓞 L) → Ideal.absNorm w = Ideal.absNorm v := by p2m_exact_reverting @_root_.P2MW.S_NumberField_ncard_primesOver_eq_finrank_of_isCyclotomicExtension_of_absNorm_modEq_one.solution
