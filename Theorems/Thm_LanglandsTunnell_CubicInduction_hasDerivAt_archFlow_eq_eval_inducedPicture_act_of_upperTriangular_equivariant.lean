import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_hasDerivAt_archFlow_eq_eval_inducedPicture_act_of_upperTriangular_equivariant

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm
open LanglandsTunnell.CubicInduction

theorem
LanglandsTunnell.CubicInduction.hasDerivAt_archFlow_eq_eval_inducedPicture_act_of_upperTriangular_equivariant
    (ν : Fin 3 → ℂ) (F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (hB : ∀ e : Fin 3 → Fin 3 → ℝ, (∀ i j : Fin 3, j < i → e i j = 0) → (∀ i : Fin 3, 0 < e i i) →
      ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
        F (WhittakerBlock.archRealLift3 e * g) =
          (∏ a : Fin 3, ((e a a : ℝ) : ℂ) ^ (ν a + (![1, 0, -1] : Fin 3 → ℂ) a)) * F g)
    (k₁ : AdelicGL 3 (𝓞 ℚ) ℚ) (hk₁ : archComponent3 (𝓞 ℚ) ℚ k₁ = 1)
    (P : MvPolynomial (Fin 3 × Fin 3) ℂ)
    (hP : ∀ o : Fin 3 → Fin 3 → ℝ, (∀ i j : Fin 3, ∑ a : Fin 3, o a i * o a j = if i = j then 1 else 0) →
      F (WhittakerBlock.archRealLift3 o * k₁) = MvPolynomial.eval (fun ij : Fin 3 × Fin 3 => ((o ij.1 ij.2 : ℝ) : ℂ)) P)
    (o : Fin 3 → Fin 3 → ℝ) (ho : ∀ i j : Fin 3, ∑ a : Fin 3, o a i * o a j = if i = j then 1 else 0)
    (c d : Fin 3) :
    let act : (Fin 3 → ℂ) → Fin 3 → Fin 3 →
        MvPolynomial (Fin 3 × Fin 3) ℂ → MvPolynomial (Fin 3 × Fin 3) ℂ :=
      fun ν c d p =>
        (∑ a : Fin 3, MvPolynomial.C (ν a + (![1, 0, -1] : Fin 3 → ℂ) a) *
            (MvPolynomial.X (a, c) * MvPolynomial.X (a, d))) * p +
        ∑ i : Fin 3, ∑ j : Fin 3,
          (∑ m : Fin 3,
            (if m < i then MvPolynomial.X (i, c) * MvPolynomial.X (m, d)
              else if i < m then -(MvPolynomial.X (m, c) * MvPolynomial.X (i, d))
              else (0 : MvPolynomial (Fin 3 × Fin 3) ℂ)) * MvPolynomial.X (m, j)) *
            MvPolynomial.pderiv (i, j) p
    HasDerivAt
      (fun s : ℝ => F (WhittakerBlock.archRealLift3 o * k₁ *
        WhittakerBlock.archRealLift3 fun a b => (if a = b then (1 : ℝ) else 0) + if a = c ∧ b = d then s else 0))
      (MvPolynomial.eval (fun ij : Fin 3 × Fin 3 => ((o ij.1 ij.2 : ℝ) : ℂ)) (act ν c d P)) 0 := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_hasDerivAt_archFlow_eq_eval_inducedPicture_act_of_upperTriangular_equivariant.solution
