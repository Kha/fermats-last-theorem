import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import P2M.Util
import P2M.Sol.S_FormalGroup_linCombAdic_mem_and_sub_natCast_mul_add_mem_sq_and_linCombAdic_zero

set_option autoImplicit false

open IsLocalRing FormalGroup

theorem FormalGroup.linCombAdic_mem_and_sub_natCast_mul_add_mem_sq_and_linCombAdic_zero
    (R : Type) [CommRing R] (I : Ideal R) [IsAdicComplete I R] (F : FormalGroup R)
    (x₀ x₁ : R) (hx₀ : x₀ ∈ I) (hx₁ : x₁ ∈ I) (a b : ℕ) :
    F.linCombAdic I x₀ x₁ a b ∈ I ∧
      F.linCombAdic I x₀ x₁ a b - ((a : R) * x₀ + (b : R) * x₁) ∈ I ^ 2 ∧
      F.linCombAdic I x₀ x₁ 0 0 = 0 := by p2m_exact_reverting @_root_.P2MW.S_FormalGroup_linCombAdic_mem_and_sub_natCast_mul_add_mem_sq_and_linCombAdic_zero.solution
