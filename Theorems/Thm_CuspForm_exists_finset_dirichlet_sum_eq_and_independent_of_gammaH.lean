import Definitions.Def_CohCarrier_Level
import Mathlib.NumberTheory.ModularForms.Basic
import Mathlib.NumberTheory.DirichletCharacter.Basic
import P2M.Util
import P2M.Sol.S_CuspForm_exists_finset_dirichlet_sum_eq_and_independent_of_gammaH

set_option autoImplicit false

open scoped MatrixGroups ModularForm

theorem CuspForm.exists_finset_dirichlet_sum_eq_and_independent_of_gammaH
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (k : ℤ) :
    (∀ f : CuspForm (CohCarrier.GammaH M H) k,
      ∃ (s : Finset (DirichletCharacter ℂ M)) (fε : DirichletCharacter ℂ M → CuspForm (CohCarrier.GammaH M H) k),
        (∀ ε ∈ s, ∀ d : (ZMod M)ˣ, d ∈ H → ε (d : ZMod M) = 1) ∧
        (∀ ε ∈ s, ∀ σ : CongruenceSubgroup.Gamma0 M,
          ⇑(fε ε) ∣[k] ((Matrix.SpecialLinearGroup.mapGL ℝ (σ : SL(2, ℤ)) : GL (Fin 2) ℝ)) =
            ε (((σ : SL(2, ℤ)) 1 1 : ℤ) : ZMod M) • ⇑(fε ε)) ∧
        ⇑f = ∑ ε ∈ s, ⇑(fε ε)) ∧
    (∀ (s : Finset (DirichletCharacter ℂ M)) (g : DirichletCharacter ℂ M → CuspForm (CohCarrier.GammaH M H) k),
      (∀ ε ∈ s, ∀ σ : CongruenceSubgroup.Gamma0 M,
          ⇑(g ε) ∣[k] ((Matrix.SpecialLinearGroup.mapGL ℝ (σ : SL(2, ℤ)) : GL (Fin 2) ℝ)) =
            ε (((σ : SL(2, ℤ)) 1 1 : ℤ) : ZMod M) • ⇑(g ε)) →
      (∑ ε ∈ s, ⇑(g ε)) = 0 → ∀ ε ∈ s, g ε = 0) := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_exists_finset_dirichlet_sum_eq_and_independent_of_gammaH.solution
