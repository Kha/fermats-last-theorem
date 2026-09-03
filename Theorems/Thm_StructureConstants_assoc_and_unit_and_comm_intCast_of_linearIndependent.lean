import Mathlib
import P2M.Util
import P2M.Sol.S_StructureConstants_assoc_and_unit_and_comm_intCast_of_linearIndependent

theorem StructureConstants.assoc_and_unit_and_comm_intCast_of_linearIndependent
    {A : Type} [Ring A] {K : ℕ} (u : Fin K → A) (hu : LinearIndependent ℤ u)
    (c : Fin K → Fin K → Fin K → ℤ) (c₁ : Fin K → ℤ)
    (hu_mul : ∀ k l : Fin K, u k * u l = ∑ m, c k l m • u m) (hu_one : ∑ m, c₁ m • u m = 1)
    (R : Type) [CommRing R] :
    (∀ (a b d : Fin K → R) (s : Fin K),
      ∑ q, ∑ t, (∑ k, ∑ l, a k * b l * (c k l q : R)) * d t * (c q t s : R) =
        ∑ k, ∑ q, a k * (∑ l, ∑ t, b l * d t * (c l t q : R)) * (c k q s : R)) ∧
    (∀ (a : Fin K → R) (s : Fin K), ∑ k, ∑ l, (c₁ k : R) * a l * (c k l s : R) = a s) ∧
    (∀ (a : Fin K → R) (s : Fin K), ∑ k, ∑ l, a k * (c₁ l : R) * (c k l s : R) = a s) ∧
    ((∀ k l : Fin K, u k * u l = u l * u k) →
      ∀ (a b : Fin K → R) (s : Fin K),
        ∑ k, ∑ l, a k * b l * (c k l s : R) = ∑ k, ∑ l, b k * a l * (c k l s : R)) := by p2m_exact_reverting @_root_.P2MW.S_StructureConstants_assoc_and_unit_and_comm_intCast_of_linearIndependent.solution
