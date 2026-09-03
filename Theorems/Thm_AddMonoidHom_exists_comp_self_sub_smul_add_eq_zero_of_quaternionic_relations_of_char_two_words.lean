import Mathlib
import P2M.Util
import P2M.Sol.S_AddMonoidHom_exists_comp_self_sub_smul_add_eq_zero_of_quaternionic_relations_of_char_two_words

set_option autoImplicit false

theorem AddMonoidHom.exists_comp_self_sub_smul_add_eq_zero_of_quaternionic_relations_of_char_two_words
    {V : Type*} [AddCommGroup V] (σ i j : V →+ V)
    (hσ3 : ∀ T, σ (σ (σ T)) = T) (hi : ∀ T, i (i T) = -T) (hj : ∀ T, j (j T) = -T)
    (hij : ∀ T, i (j T) = -(j (i T))) (hσi : ∀ T, σ (i T) = j (σ T)) (hσj : ∀ T, σ (j T) = j (i (σ T)))
    (hσ : ∀ T, σ (σ T) + σ T + T = 0)
    (m : V →+ V)
    (hm : m = AddMonoidHom.id _ ∨ m = σ ∨ m = σ.comp σ ∨
        m = i ∨ m = i.comp σ ∨ m = i.comp (σ.comp σ) ∨
        m = j ∨ m = j.comp σ ∨ m = j.comp (σ.comp σ) ∨
        m = i.comp j ∨ m = (i.comp j).comp σ ∨ m = (i.comp j).comp (σ.comp σ)) :
    ∃ t : ℤ, (t = -1 ∨ t = 0 ∨ t = 1 ∨ t = 2) ∧ (t = 2 → m = AddMonoidHom.id _) ∧
      ∀ T, m (m T) - t • m T + T = 0 := by p2m_exact_reverting @_root_.P2MW.S_AddMonoidHom_exists_comp_self_sub_smul_add_eq_zero_of_quaternionic_relations_of_char_two_words.solution
