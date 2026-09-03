import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_ArchDerivCasimirComplex
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_su2Strings_of_finiteDimensional_of_isArchSmoothAtComplex

set_option autoImplicit false

open NumberField AutomorphicForm NumberField.InfinitePlace NumberField.InfinitePlace.Completion

theorem AutomorphicForm.exists_su2Strings_of_finiteDimensional_of_isArchSmoothAtComplex
    (F : Type) [Field F] [NumberField F] {w : InfinitePlace F} (hw : w.IsComplex)
    (Y : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)) [FiniteDimensional ℂ Y]
    (hYs : ∀ y ∈ Y, IsArchSmoothAtComplex hw y)
    (hYK : ∀ (k : rowIsometrySubgroup₀ w.Completion), ∀ y ∈ Y,
      (fun g => y (g * rowIsometryInclAt₀ F w k)) ∈ Y) :
    ∃ (m : ℕ) (n : Fin m → ℕ) (x : Fin m → ℕ → (AdelicGL2 (𝓞 F) F → ℂ)),
      (∀ s p, x s p ∈ Y) ∧
      (∀ s p, n s < p → x s p = 0) ∧
      LinearIndependent ℂ (fun sp : (Σ s : Fin m, Fin (n s + 1)) => x sp.1 sp.2) ∧
      (∀ y ∈ Y, ∃ coef : (s : Fin m) → Fin (n s + 1) → ℂ, y = ∑ s, ∑ p : Fin (n s + 1), coef s p • x s p) ∧
      (∀ s p, archDerivAtComplex hw .iH (x s p) = (Complex.I * ((n s : ℂ) - 2 * (p : ℂ))) • x s p) ∧
      (∀ s p, archDerivAtComplex hw .Fm (x s p) - archDerivAtComplex hw .E (x s p) =
        x s (p + 1) - ((p : ℂ) * ((n s : ℂ) + 1 - (p : ℂ))) • x s (p - 1)) ∧
      (∀ s p, archDerivAtComplex hw .iE (x s p) + archDerivAtComplex hw .iFm (x s p) =
        Complex.I • (x s (p + 1) + ((p : ℂ) * ((n s : ℂ) + 1 - (p : ℂ))) • x s (p - 1))) ∧
      (∀ s p, p ≤ n s → HasCircleWeightAt hw ((n s : ℤ) - 2 * (p : ℤ)) (x s p)) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_su2Strings_of_finiteDimensional_of_isArchSmoothAtComplex.solution
