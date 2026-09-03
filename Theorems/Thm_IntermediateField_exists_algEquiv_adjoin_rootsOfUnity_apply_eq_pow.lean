import Mathlib
import P2M.Util
import P2M.Sol.S_IntermediateField_exists_algEquiv_adjoin_rootsOfUnity_apply_eq_pow

set_option autoImplicit false
open IntermediateField
theorem IntermediateField.exists_algEquiv_adjoin_rootsOfUnity_apply_eq_pow {F E : Type} [Field F] [Field E] [Algebra F E] (m : ℕ) (hm : 0 < m) (ζ₀ : E) (hζ₀ : IsPrimitiveRoot ζ₀ m)
    (a : ℕ) (ha : a.Coprime m) (hroot : Polynomial.aeval (ζ₀ ^ a) (minpoly F ζ₀) = 0) :
    ∃ φ : (IntermediateField.adjoin F {ζ : E | ζ ^ m = 1}) ≃ₐ[F] (IntermediateField.adjoin F {ζ : E | ζ ^ m = 1}),
      ∀ ζ : IntermediateField.adjoin F {ζ : E | ζ ^ m = 1}, (ζ : E) ^ m = 1 → (φ ζ : E) = (ζ : E) ^ a := by p2m_exact_reverting @_root_.P2MW.S_IntermediateField_exists_algEquiv_adjoin_rootsOfUnity_apply_eq_pow.solution
