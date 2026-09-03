import Mathlib
import P2M.Util
import P2M.Sol.S_CommRing_exists_etale_faithfullyFlat_units_eq_mul_inv_mul_inv_of_symm_of_cocycle_of_isUnit_card

set_option autoImplicit false

theorem CommRing.exists_etale_faithfullyFlat_units_eq_mul_inv_mul_inv_of_symm_of_cocycle_of_isUnit_card
    (R : Type) [CommRing R] {K : Type} [AddCommGroup K] [Fintype K]
    (hK : IsUnit ((Fintype.card K : ℕ) : R))
    (c : K → K → Rˣ) (hsymm : ∀ a b : K, c a b = c b a)
    (hcocycle : ∀ a b k : K, c a b * c (a + b) k = c b k * c a (b + k)) :
    ∃ (R' : Type) (_ : CommRing R') (_ : Algebra R R'), Module.FaithfullyFlat R R' ∧ Algebra.Etale R R' ∧
      ∃ b : K → R'ˣ, ∀ k k' : K,
        Units.map (algebraMap R R').toMonoidHom (c k k') = b (k + k') * (b k)⁻¹ * (b k')⁻¹ := by p2m_exact_reverting @_root_.P2MW.S_CommRing_exists_etale_faithfullyFlat_units_eq_mul_inv_mul_inv_of_symm_of_cocycle_of_isUnit_card.solution
