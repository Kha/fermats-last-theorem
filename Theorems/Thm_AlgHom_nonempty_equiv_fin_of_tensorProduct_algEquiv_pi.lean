import Mathlib
import P2M.Util
import P2M.Sol.S_AlgHom_nonempty_equiv_fin_of_tensorProduct_algEquiv_pi

universe u v w w'

open TensorProduct

theorem AlgHom.nonempty_equiv_fin_of_tensorProduct_algEquiv_pi
    {A : Type u} [CommRing A] {R' : Type v} [CommRing R'] [Algebra A R']
    {B : Type w} [CommRing B] [Algebra A B] {d : ℕ}
    (φ : R' ⊗[A] B ≃ₐ[R'] (Fin d → R'))
    {Ω : Type w'} [Field Ω] [Algebra A Ω] (t₀ : R' →ₐ[A] Ω) :
    Nonempty ((B →ₐ[A] Ω) ≃ Fin d) := by p2m_exact_reverting @_root_.P2MW.S_AlgHom_nonempty_equiv_fin_of_tensorProduct_algEquiv_pi.solution
