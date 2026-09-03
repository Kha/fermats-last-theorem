import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Theorems.Thm_QuaternionAlgebra_forall_isUnit_iff_forall_normForm_eq_zero
import Theorems.Thm_QuaternionAlgebra_nonempty_tensorProduct_adicCompletion_ringEquiv
import P2M.Util
namespace P2MW.S_QuaternionAlgebra_forall_tensorProduct_adicCompletion_isUnit_iff_forall_normForm_eq_zero

set_option autoImplicit false

open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField

namespace E1Chi

theorem forall_isUnit_iff_of_ringEquiv {A B : Type} [Ring A] [Ring B] (e : A ≃+* B) :
    (∀ x : A, x ≠ 0 → IsUnit x) ↔ ∀ y : B, y ≠ 0 → IsUnit y := by
  constructor
  · intro h y hy
    have hx : e.symm y ≠ 0 := fun h0 => hy (by simpa using congrArg e h0)
    have := (h _ hx).map e
    simpa using this
  · intro h x hx
    have hy : e x ≠ 0 := fun h0 => hx (by simpa using congrArg e.symm h0)
    have := (h _ hy).map e.symm
    simpa using this

theorem main (a b : ℚ) (v : HeightOneSpectrum (𝓞 ℚ)) :
    (∀ x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ, x ≠ 0 → IsUnit x) ↔
      ∀ x₀ x₁ x₂ x₃ : v.adicCompletion ℚ,
        x₀ ^ 2 - (a : v.adicCompletion ℚ) * x₁ ^ 2 - (b : v.adicCompletion ℚ) * x₂ ^ 2 +
            (a : v.adicCompletion ℚ) * (b : v.adicCompletion ℚ) * x₃ ^ 2 = 0 →
          x₀ = 0 ∧ x₁ = 0 ∧ x₂ = 0 ∧ x₃ = 0 := by
  obtain ⟨e⟩ := QuaternionAlgebra.nonempty_tensorProduct_adicCompletion_ringEquiv a b v
  rw [forall_isUnit_iff_of_ringEquiv e]
  exact QuaternionAlgebra.forall_isUnit_iff_forall_normForm_eq_zero (v.adicCompletion ℚ) _ _

end E1Chi

theorem solution
    (a b : ℚ) (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ)) :
    (∀ x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ, x ≠ 0 → IsUnit x) ↔
      ∀ x₀ x₁ x₂ x₃ : v.adicCompletion ℚ,
        x₀ ^ 2 - (a : v.adicCompletion ℚ) * x₁ ^ 2 - (b : v.adicCompletion ℚ) * x₂ ^ 2 +
            (a : v.adicCompletion ℚ) * (b : v.adicCompletion ℚ) * x₃ ^ 2 = 0 →
          x₀ = 0 ∧ x₁ = 0 ∧ x₂ = 0 ∧ x₃ = 0 :=
  E1Chi.main a b v
