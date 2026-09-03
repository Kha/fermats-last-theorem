import Definitions.Def_AutomorphicForm_CuspidalConstituent
import P2M.Util
import P2M.Sol.S_AutomorphicForm_isFactorizableTestFn_sum_mul_comp_mul_mul

set_option autoImplicit false

open MeasureTheory NumberField AutomorphicForm AutomorphicForm.CuspidalConstituent
open scoped BigOperators

theorem AutomorphicForm.isFactorizableTestFn_sum_mul_comp_mul_mul
    (F : Type) [Field F] [NumberField F]
    {f : AdelicGL2 (𝓞 F) F → ℂ} (hf : IsFactorizableTestFn F f) {n : ℕ} (c : Fin n → ℂ)
    (a b : Fin n → AdelicGL2 (𝓞 F) F)
    (ha : ∀ i, a i ∈ (⨆ w : InfinitePlace F, (rowIsometryInclAt₀ F w).range))
    (hb : ∀ i, b i ∈ (⨆ w : InfinitePlace F, (rowIsometryInclAt₀ F w).range)) :
    IsFactorizableTestFn F (fun y => ∑ i, c i * f (a i * y * b i)) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_isFactorizableTestFn_sum_mul_comp_mul_mul.solution
