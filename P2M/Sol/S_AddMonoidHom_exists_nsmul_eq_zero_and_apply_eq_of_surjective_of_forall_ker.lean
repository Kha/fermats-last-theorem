import Mathlib
import P2M.Util
namespace P2MW.S_AddMonoidHom_exists_nsmul_eq_zero_and_apply_eq_of_surjective_of_forall_ker

set_option autoImplicit false

theorem solution
    {A B : Type*} [AddCommGroup A] [AddCommGroup B] (f : A →+ B)
    (hf : Function.Surjective f)
    (m : ℕ) (hdiv : ∀ k : A, f k = 0 → ∃ j : A, f j = 0 ∧ m • j = k)
    (b : B) (hmb : m • b = 0) :
    ∃ a : A, m • a = 0 ∧ f a = b := by
  obtain ⟨a₀, ha₀⟩ := hf b
  have hker : f (m • a₀) = 0 := by rw [map_nsmul, ha₀, hmb]
  obtain ⟨j, hjker, hmj⟩ := hdiv (m • a₀) hker
  exact ⟨a₀ - j, by rw [smul_sub, hmj, sub_self], by rw [map_sub, ha₀, hjker, sub_zero]⟩
