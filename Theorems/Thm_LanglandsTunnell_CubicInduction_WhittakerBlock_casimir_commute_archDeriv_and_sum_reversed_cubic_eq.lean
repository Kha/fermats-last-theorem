import Definitions.Def_LanglandsTunnell_CubicInduction_EnvelopingAction3
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_WhittakerBlock_casimir_commute_archDeriv_and_sum_reversed_cubic_eq

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm

theorem LanglandsTunnell.CubicInduction.WhittakerBlock.casimir_commute_archDeriv_and_sum_reversed_cubic_eq :
    (∀ a b : Fin 3, Commute (∑ i : Fin 3, archDerivₗ i i) (archDerivₗ a b)) ∧
    (∀ a b : Fin 3, Commute (∑ i : Fin 3, ∑ j : Fin 3, archDerivₗ i j * archDerivₗ j i) (archDerivₗ a b)) ∧
    (∀ a b : Fin 3,
      Commute (∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, archDerivₗ i j * archDerivₗ j k * archDerivₗ k i)
        (archDerivₗ a b)) ∧
    (∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, archDerivₗ j i * archDerivₗ k j * archDerivₗ i k =
      (∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, archDerivₗ i j * archDerivₗ j k * archDerivₗ k i) +
        (∑ i : Fin 3, archDerivₗ i i) * (∑ i : Fin 3, archDerivₗ i i) -
        (3 : ℂ) • ∑ i : Fin 3, ∑ j : Fin 3, archDerivₗ i j * archDerivₗ j i) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_WhittakerBlock_casimir_commute_archDeriv_and_sum_reversed_cubic_eq.solution
