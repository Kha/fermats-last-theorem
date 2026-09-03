import Mathlib
import Theorems.Thm_CommGroup_exists_forall_monoidHom_exists_apply_eq_mul_inv_mul_inv_of_symm_of_cocycle
import Theorems.Thm_Algebra_exists_etale_faithfullyFlat_finite_forall_exists_units_pow_eq_of_isUnit
import P2M.Util
namespace P2MW.S_CommRing_exists_etale_faithfullyFlat_units_eq_mul_inv_mul_inv_of_symm_of_cocycle_of_isUnit_card

set_option autoImplicit false

theorem solution
    (R : Type) [CommRing R] {K : Type} [AddCommGroup K] [Fintype K]
    (hK : IsUnit ((Fintype.card K : ℕ) : R))
    (c : K → K → Rˣ) (hsymm : ∀ a b : K, c a b = c b a)
    (hcocycle : ∀ a b k : K, c a b * c (a + b) k = c b k * c a (b + k)) :
    ∃ (R' : Type) (_ : CommRing R') (_ : Algebra R R'), Module.FaithfullyFlat R R' ∧ Algebra.Etale R R' ∧
      ∃ b : K → R'ˣ, ∀ k k' : K,
        Units.map (algebraMap R R').toMonoidHom (c k k') = b (k + k') * (b k)⁻¹ * (b k')⁻¹ := by
  classical
  obtain ⟨m, a, n, hn, H⟩ :=
    CommGroup.exists_forall_monoidHom_exists_apply_eq_mul_inv_mul_inv_of_symm_of_cocycle c hsymm hcocycle
  have hnu : ∀ i, IsUnit ((n i : ℕ) : R) := by
    intro i
    obtain ⟨q, hq⟩ := (hn i).2
    rw [Nat.card_eq_fintype_card] at hq
    have : ((Fintype.card K : ℕ) : R) = (n i : R) * (q : R) := by rw [hq, Nat.cast_mul]
    exact isUnit_of_mul_isUnit_left (by rw [← this]; exact hK)
  obtain ⟨R', _, _, _, _, _, v, hv⟩ :=
    Algebra.exists_etale_faithfullyFlat_finite_forall_exists_units_pow_eq_of_isUnit R n (fun i => (hn i).1) hnu a
  obtain ⟨b, hb⟩ := H R'ˣ (Units.map (algebraMap R R' : R →* R')) (fun i => ⟨v i, hv i⟩)
  exact ⟨R', inferInstance, inferInstance, inferInstance, inferInstance, b, hb⟩
