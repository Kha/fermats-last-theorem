import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_BorelSubgroup
import Definitions.Def_LanglandsTunnell_TateLocalZeta
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_sum_mul_localZeta_bottomRow_eq_of_rightTranslatesSpanFinite

set_option autoImplicit false

open MeasureTheory NumberField NumberField.InfinitePlace
open AutomorphicForm AutomorphicForm.WindowedSiegel LanglandsTunnell.TateLocal

theorem AutomorphicForm.exists_sum_mul_localZeta_bottomRow_eq_of_rightTranslatesSpanFinite
    (F : Type) [Field F] [NumberField F] (w : InfinitePlace F)
    [MeasurableSpace w.Completion] [BorelSpace w.Completion]
    (μa : Measure w.Completion) [μa.IsAddHaarMeasure]
    (η₁ η₂ : (w.Completion)ˣ →* ℂˣ)
    (_h₁ : ∀ x, ‖((η₁ x : ℂˣ) : ℂ)‖ = 1) (_h₂ : ∀ x, ‖((η₂ x : ℂˣ) : ℂ)‖ = 1)
    (_h₁c : Continuous fun x : (w.Completion)ˣ => ((η₁ x : ℂˣ) : ℂ))
    (_h₂c : Continuous fun x : (w.Completion)ˣ => ((η₂ x : ℂˣ) : ℂ))
    (f : GL (Fin 2) w.Completion → ℂ) (_hfc : Continuous f)
    (_hfK : RightTranslatesSpanFinite (rowIsometrySubgroup w.Completion) f)
    (_hfB : ∀ (b : GL (Fin 2) w.Completion) (hb : b ∈ borelSubgroup w.Completion), IsRowIsometry b →
        ∀ g : GL (Fin 2) w.Completion, IsRowIsometry g →
          f (b * g) = ((η₁ (borelDiagFst (⟨b, hb⟩ : ↥(borelSubgroup w.Completion))) : ℂˣ) : ℂ)
            * ((η₂ (borelDiagSnd (⟨b, hb⟩ : ↥(borelSubgroup w.Completion))) : ℂˣ) : ℂ) * f g) :
    ∃ (m : ℕ) (Φ : Fin m → (Fin 2 → w.Completion) → ℂ) (e : Fin m → ℂ → ℂ),
      (∀ j, Differentiable ℂ (e j)) ∧
      (∀ j, ∃ P : MvPolynomial (Fin 2 ⊕ Fin 2) ℂ, ∀ y : Fin 2 → w.Completion,
        Φ j y = MvPolynomial.eval
              (Sum.elim (fun i => Completion.extensionEmbedding w (y i))
                (fun i => starRingEnd ℂ (Completion.extensionEmbedding w (y i)))) P
            * Complex.exp (-(Real.pi : ℂ) * ∑ i, (((‖y i‖ ^ 2 : ℝ)) : ℂ))) ∧
      ∀ z : ℂ, 0 < z.re →
        ∀ k : GL (Fin 2) w.Completion, IsRowIsometry k →
          (∑ j, e j z * (((η₁ (Matrix.GeneralLinearGroup.det k) : ℂˣ) : ℂ)
              * localZeta μa (fun t => Φ j (fun i => t * (k : Matrix (Fin 2) (Fin 2) w.Completion) 1 i))
                  (η₁ * η₂⁻¹) z))
            = f k := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_sum_mul_localZeta_bottomRow_eq_of_rightTranslatesSpanFinite.solution
