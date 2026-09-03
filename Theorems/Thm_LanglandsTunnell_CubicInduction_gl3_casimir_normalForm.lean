import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_gl3_casimir_normalForm

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm

theorem LanglandsTunnell.CubicInduction.gl3_casimir_normalForm
    {A : Type*} [Ring A] [Algebra ℂ A] (e : Fin 3 → Fin 3 → A)
    (he : ∀ i j k l : Fin 3,
      e i j * e k l - e k l * e i j = (if j = k then e i l else 0) - (if l = i then e k j else 0)) :
    (∑ i : Fin 3, ∑ j : Fin 3, e i j * e j i =
      (e 0 0 * e 0 0 + e 1 1 * e 1 1 + e 2 2 * e 2 2 - 2 • e 0 0 + 2 • e 2 2) +
        (e 0 1 * (2 • e 1 0) + e 0 2 * (2 • e 2 0) + e 1 2 * (2 • e 2 1))) ∧
    (∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, e i j * (e j k * e k i) =
      (e 0 0 * e 0 0 * e 0 0 + e 1 1 * e 1 1 * e 1 1 + e 2 2 * e 2 2 * e 2 2
        - 2 • (e 0 0 * e 0 0) + e 1 1 * e 1 1 + 4 • (e 2 2 * e 2 2)
        - (e 0 0 * e 1 1 + e 0 0 * e 2 2 + e 1 1 * e 2 2)
        - 2 • e 0 0 - 2 • e 1 1 + 4 • e 2 2) +
      (e 0 1 * (3 • (e 0 0 * e 1 0 + e 1 1 * e 1 0 + e 1 2 * e 2 0)) +
        e 0 2 * (3 • (e 0 0 * e 2 0 + e 1 0 * e 2 1 + e 2 0 + e 2 2 * e 2 0)) +
        e 1 2 * (3 • (e 1 1 * e 2 1 + 2 • e 2 1 + e 2 2 * e 2 1)))) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_gl3_casimir_normalForm.solution
