import Mathlib
import P2M.Util
import P2M.Sol.S_Polynomial_isDomain_tensor_of_isFractionRing

open Polynomial
open scoped TensorProduct

universe u₁ u₂ u₃

theorem Polynomial.isDomain_tensor_of_isFractionRing
    (F₀ : Type u₁) (κ : Type u₂) (k : Type u₃) [Field F₀] [CommRing κ] [Field k]
    [Algebra F₀[X] κ] [IsFractionRing F₀[X] κ] [Algebra F₀ κ] [IsScalarTower F₀ F₀[X] κ]
    [Algebra F₀ k] : IsDomain (κ ⊗[F₀] k) := by p2m_exact_reverting @_root_.P2MW.S_Polynomial_isDomain_tensor_of_isFractionRing.solution
