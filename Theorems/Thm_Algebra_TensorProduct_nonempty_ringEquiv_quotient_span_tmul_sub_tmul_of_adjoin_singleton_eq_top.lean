import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_TensorProduct_nonempty_ringEquiv_quotient_span_tmul_sub_tmul_of_adjoin_singleton_eq_top

set_option autoImplicit false

open TensorProduct

theorem Algebra.TensorProduct.nonempty_ringEquiv_quotient_span_tmul_sub_tmul_of_adjoin_singleton_eq_top
    (Z₀ : Type) [CommRing Z₀] (V : Type) [CommRing V] [Algebra Z₀ V] (ϖ : V) (hgen : Algebra.adjoin Z₀ {ϖ} = ⊤)
    (A : Type) [CommRing A] [Algebra Z₀ A] [Algebra V A] [IsScalarTower Z₀ V A]
    (C : Type) [CommRing C] [Algebra Z₀ C] [Algebra V C] [IsScalarTower Z₀ V C]
    (μ : A) (w : C) (hA : algebraMap V A ϖ = 1 - μ) (hC : algebraMap V C ϖ = 1 - w) :
    ∃ e : ((A ⊗[Z₀] C) ⧸ Ideal.span {(μ ⊗ₜ[Z₀] (1 : C)) - ((1 : A) ⊗ₜ[Z₀] w)}) ≃+* (C ⊗[V] A),
      ∀ (a : A) (c : C), e (Ideal.Quotient.mk _ (a ⊗ₜ[Z₀] c)) = c ⊗ₜ[V] a := by p2m_exact_reverting @_root_.P2MW.S_Algebra_TensorProduct_nonempty_ringEquiv_quotient_span_tmul_sub_tmul_of_adjoin_singleton_eq_top.solution
