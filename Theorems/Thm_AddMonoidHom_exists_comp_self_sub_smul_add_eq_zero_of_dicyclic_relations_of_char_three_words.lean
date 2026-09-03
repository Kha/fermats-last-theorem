import Mathlib
import P2M.Util
import P2M.Sol.S_AddMonoidHom_exists_comp_self_sub_smul_add_eq_zero_of_dicyclic_relations_of_char_three_words

set_option autoImplicit false

theorem AddMonoidHom.exists_comp_self_sub_smul_add_eq_zero_of_dicyclic_relations_of_char_three_words
    {V : Type*} [AddCommGroup V] (α β : V →+ V)
    (hα : ∀ T, α (α T) = -T) (hβ : ∀ T, β (β T) + β T + T = 0) (hαβ : ∀ T, α (β T) = β (β (α T)))
    (m : V →+ V)
    (hm : m = AddMonoidHom.id _ ∨ m = α ∨ m = β ∨ m = β.comp β ∨ m = α.comp β ∨ m = α.comp (β.comp β)) :
    ∃ t : ℤ, (t = -1 ∨ t = 0 ∨ t = 1 ∨ t = 2) ∧ (t = 2 → m = AddMonoidHom.id _) ∧
      ∀ T, m (m T) - t • m T + T = 0 := by p2m_exact_reverting @_root_.P2MW.S_AddMonoidHom_exists_comp_self_sub_smul_add_eq_zero_of_dicyclic_relations_of_char_three_words.solution
