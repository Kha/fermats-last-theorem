import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import P2M.Util
namespace P2MW.S_QuaternionAlgebra_forall_tensorProduct_adicCompletion_isUnit_iff_of_algEquiv

set_option autoImplicit false

open scoped Quaternion TensorProduct
open IsDedekindDomain NumberField

namespace TransferLocal

theorem transfer {A B C : Type} [Ring A] [Ring B] [CommRing C] [Algebra ℚ A] [Algebra ℚ B] [Algebra ℚ C]
    (e : A ≃ₐ[ℚ] B) (h : ∀ x : A ⊗[ℚ] C, x ≠ 0 → IsUnit x) : ∀ x : B ⊗[ℚ] C, x ≠ 0 → IsUnit x := by
  intro x hx
  let E : A ⊗[ℚ] C ≃ₐ[ℚ] B ⊗[ℚ] C := Algebra.TensorProduct.congr e AlgEquiv.refl
  have hx' : E.symm x ≠ 0 := by
    intro h0
    apply hx
    simpa using congrArg E h0
  have hu := h (E.symm x) hx'
  simpa using hu.map E

end TransferLocal

theorem solution
    {a b a' b' : ℚ} (e : ℍ[ℚ, a, b] ≃ₐ[ℚ] ℍ[ℚ, a', b']) (v : HeightOneSpectrum (𝓞 ℚ)) :
    (∀ x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ, x ≠ 0 → IsUnit x) ↔
      (∀ x : ℍ[ℚ, a', b'] ⊗[ℚ] v.adicCompletion ℚ, x ≠ 0 → IsUnit x) :=
  ⟨TransferLocal.transfer e, TransferLocal.transfer e.symm⟩
