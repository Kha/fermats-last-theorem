import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_isAlgebraic_zmod_quotient_of_card_quotient_eq_of_forall_exists_monic_aeval_mem

set_option autoImplicit false

theorem Algebra.isAlgebraic_zmod_quotient_of_card_quotient_eq_of_forall_exists_monic_aeval_mem
    {r : ℕ} [Fact r.Prime]
    (𝒪 : Type) [CommRing 𝒪] (π : 𝒪) (hres : Nat.card (𝒪 ⧸ Ideal.span {π}) = r)
    (Onr : Type) [CommRing Onr] [Algebra 𝒪 Onr]
    (hOnr_alg : ∀ x : Onr, ∃ p : Polynomial 𝒪, p.Monic ∧ Polynomial.aeval x p ∈ Ideal.span {algebraMap 𝒪 Onr π})
    [CharP (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) r] :
    letI : Algebra (ZMod r) (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) :=
      (ZMod.castHom (dvd_refl r) (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π})).toAlgebra
    Algebra.IsAlgebraic (ZMod r) (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) := by p2m_exact_reverting @_root_.P2MW.S_Algebra_isAlgebraic_zmod_quotient_of_card_quotient_eq_of_forall_exists_monic_aeval_mem.solution
