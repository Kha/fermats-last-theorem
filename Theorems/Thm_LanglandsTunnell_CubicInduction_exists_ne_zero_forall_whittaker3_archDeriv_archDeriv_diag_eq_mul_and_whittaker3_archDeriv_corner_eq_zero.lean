import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_exists_ne_zero_forall_whittaker3_archDeriv_archDeriv_diag_eq_mul_and_whittaker3_archDeriv_corner_eq_zero
attribute [-instance] WhittakerBlock.sigmaCompactSpace_adelicGL3 M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion M4aHerbrand.Bridge.instT2SpaceAdeleRing
attribute [-simp] LanglandsTunnell.CubicInduction.WhittakerBlock.coe_archDerivₗ_apply

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm
p2m_open "LanglandsTunnell.CubicInduction~exists_ne_zero_forall_mul_whittaker3_diag_eq_whittaker3_archDeriv~whittaker3_iterate_archDeriv_eq_iterate_archDeriv_whittaker3"

theorem LanglandsTunnell.CubicInduction.exists_ne_zero_forall_whittaker3_archDeriv_archDeriv_diag_eq_mul_and_whittaker3_archDeriv_corner_eq_zero :
    ∃ lam : ℂ, lam ≠ 0 ∧ ∀ (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ), WhittakerBlock.IsArchSmooth3 φ →
      (∀ w : List (Fin 3 × Fin 3),
        Continuous (List.foldr (fun ij ψ => WhittakerBlock.archDeriv ij.1 ij.2 ψ) φ w)) →
      (∀ (γ : GL (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), φ (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = φ g) →
      ∀ y₁ y₂ : ℝ, 0 < y₁ → 0 < y₂ →
      whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
          NumberField.StandardAddChar.psiQ (WhittakerBlock.archDeriv 0 1 (WhittakerBlock.archDeriv 1 2 φ))
          (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0)) =
        lam ^ 2 * (y₁ : ℂ) * (y₂ : ℂ) *
          whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
          NumberField.StandardAddChar.psiQ φ
            (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0)) ∧
      whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
          NumberField.StandardAddChar.psiQ (WhittakerBlock.archDeriv 0 2 φ)
          (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0)) = 0 := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_exists_ne_zero_forall_whittaker3_archDeriv_archDeriv_diag_eq_mul_and_whittaker3_archDeriv_corner_eq_zero.solution
