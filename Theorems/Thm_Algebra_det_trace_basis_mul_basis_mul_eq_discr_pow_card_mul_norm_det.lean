import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_det_trace_basis_mul_basis_mul_eq_discr_pow_card_mul_norm_det

set_option autoImplicit false

theorem Algebra.det_trace_basis_mul_basis_mul_eq_discr_pow_card_mul_norm_det
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (b : Module.Basis ι R S) (G : Matrix κ κ S) :
    (Matrix.of fun p q : ι × κ => Algebra.trace R S (b p.1 * b q.1 * G p.2 q.2)).det =
      Algebra.discr R b ^ Fintype.card κ * Algebra.norm R G.det := by p2m_exact_reverting @_root_.P2MW.S_Algebra_det_trace_basis_mul_basis_mul_eq_discr_pow_card_mul_norm_det.solution
