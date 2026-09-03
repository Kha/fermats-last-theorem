import Mathlib
import Definitions.Def_QuaternionAlgebra_Order
import P2M.Util
import P2M.Sol.S_QuaternionAlgebra_IsOrder_apply_add_pow_eq_intCast_of_add_star_eq_of_forall_isUnit
attribute [-simp] QuaternionAlgebra.nrd_coe QuaternionAlgebra.nrd_one QuaternionAlgebra.trd_mk QuaternionAlgebra.nrd_mk QuaternionAlgebra.nrd_neg QuaternionAlgebra.nrd_zero QuaternionAlgebra.nrd_star

set_option autoImplicit false

p2m_open "Quaternion QuaternionAlgebra~trd IsDedekindDomain NumberField"
open scoped TensorProduct

theorem QuaternionAlgebra.IsOrder.apply_add_pow_eq_intCast_of_add_star_eq_of_forall_isUnit
    {a b : ℚ} (q : ℕ) [Fact q.Prime]
    (hq : ∀ v : HeightOneSpectrum (𝓞 ℚ), (q : 𝓞 ℚ) ∈ v.asIdeal →
      ∀ x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ, x ≠ 0 → IsUnit x)
    (O : Submodule ℤ ℍ[ℚ, a, b]) (hO : QuaternionAlgebra.IsOrder O)
    (F : Type*) [Field F] [CharP F q] (χ : ↥O → F)
    (h1 : ∀ h : (1 : ℍ[ℚ, a, b]) ∈ O, χ ⟨1, h⟩ = 1)
    (hadd : ∀ x y : ↥O, χ (x + y) = χ x + χ y)
    (hmul : ∀ (x y : ↥O) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ O),
      χ ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ = χ x * χ y)
    (x : ↥O) (n : ℤ) (hn : (x : ℍ[ℚ, a, b]) + star (x : ℍ[ℚ, a, b]) = ((n : ℚ) : ℍ[ℚ, a, b])) :
    χ x + χ x ^ q = (n : F) := by p2m_exact_reverting @_root_.P2MW.S_QuaternionAlgebra_IsOrder_apply_add_pow_eq_intCast_of_add_star_eq_of_forall_isUnit.solution
