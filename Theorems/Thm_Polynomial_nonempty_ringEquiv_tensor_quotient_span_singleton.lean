import Mathlib
import P2M.Util
import P2M.Sol.S_Polynomial_nonempty_ringEquiv_tensor_quotient_span_singleton

open Polynomial
open scoped TensorProduct

universe u₁ u₂

theorem Polynomial.nonempty_ringEquiv_tensor_quotient_span_singleton
    (κ : Type u₁) (D : Type u₂) [CommRing κ] [CommRing D] [Algebra κ D] (f : κ[X]) :
    Nonempty (D ⊗[κ] (κ[X] ⧸ Ideal.span {f}) ≃+* D[X] ⧸ Ideal.span {f.map (algebraMap κ D)}) := by p2m_exact_reverting @_root_.P2MW.S_Polynomial_nonempty_ringEquiv_tensor_quotient_span_singleton.solution
