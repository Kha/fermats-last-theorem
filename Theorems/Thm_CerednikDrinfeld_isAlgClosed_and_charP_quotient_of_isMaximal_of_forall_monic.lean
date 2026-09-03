import Mathlib
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_isAlgClosed_and_charP_quotient_of_isMaximal_of_forall_monic

set_option autoImplicit false

theorem CerednikDrinfeld.isAlgClosed_and_charP_quotient_of_isMaximal_of_forall_monic
    {r : ℕ} [Fact r.Prime]
    (𝒪 : Type) [CommRing 𝒪] (π : 𝒪) (hunr : Ideal.span {((r : ℕ) : 𝒪)} = Ideal.span {π})
    (Onr : Type) [CommRing Onr] [Algebra 𝒪 Onr]
    (hOnr_max : (Ideal.span {algebraMap 𝒪 Onr π}).IsMaximal)
    (hOnr_closed : ∀ p : Polynomial Onr, p.Monic → 0 < p.natDegree → ∃ x : Onr, Polynomial.eval x p ∈ Ideal.span {algebraMap 𝒪 Onr π}) :
    @IsAlgClosed (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) (@Ideal.Quotient.field Onr _ (Ideal.span {algebraMap 𝒪 Onr π}) hOnr_max) ∧
      CharP (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) r := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_isAlgClosed_and_charP_quotient_of_isMaximal_of_forall_monic.solution
