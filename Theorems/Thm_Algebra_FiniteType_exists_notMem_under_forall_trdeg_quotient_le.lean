import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_FiniteType_exists_notMem_under_forall_trdeg_quotient_le

set_option autoImplicit false

universe u v

theorem Algebra.FiniteType.exists_notMem_under_forall_trdeg_quotient_le
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B] [Algebra.FiniteType A B]
    (𝔮 : Ideal B) [𝔮.IsPrime] :
    ∃ s : A, s ∉ 𝔮.under A ∧ ∀ (𝔔 : Ideal B) [𝔔.IsPrime], 𝔮 ≤ 𝔔 → s ∉ 𝔔.under A →
      Algebra.trdeg (A ⧸ 𝔔.under A) (B ⧸ 𝔔) ≤ Algebra.trdeg (A ⧸ 𝔮.under A) (B ⧸ 𝔮) := by p2m_exact_reverting @_root_.P2MW.S_Algebra_FiniteType_exists_notMem_under_forall_trdeg_quotient_le.solution
