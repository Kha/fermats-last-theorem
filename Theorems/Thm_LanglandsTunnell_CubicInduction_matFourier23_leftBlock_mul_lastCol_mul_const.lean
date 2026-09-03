import Definitions.Def_LanglandsTunnell_CubicInduction_GodementSection
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries2
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_AdelicDock_LocalEmbedding
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_matFourier23_leftBlock_mul_lastCol_mul_const

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory AutomorphicForm LanglandsTunnell.TateLocal
  LanglandsTunnell.CubicInduction NumberField.StandardAddChar
open NumberField.AdelicLevel (diagOne)

theorem LanglandsTunnell.CubicInduction.matFourier23_leftBlock_mul_lastCol_mul_const
    (p : HeightOneSpectrum (𝓞 ℚ)) (η : AddChar (p.adicCompletion ℚ) ℂ)
    (φ₁ : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ) → ℂ) (φ₂ : (p.adicCompletion ℚ) × (p.adicCompletion ℚ) → ℂ) (c : ℂ) (X : Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ)) :
    letI : MeasurableSpace (p.adicCompletion ℚ) := localBorel ℚ p
    matFourier23 p η (fun Y : Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ) => φ₁ (Matrix.of fun a b => Y a (Fin.castSucc b)) * φ₂ (Y 0 2, Y 1 2) * c) X =
      matFourier22 p η φ₁ (Matrix.of fun a b => X a (Fin.castSucc b)) *
        (∫ u : (p.adicCompletion ℚ) × (p.adicCompletion ℚ), φ₂ u * η (u.1 * X 0 2 + u.2 * X 1 2) ∂((selfDualHaarAt ℚ p).prod (selfDualHaarAt ℚ p))) * c := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_matFourier23_leftBlock_mul_lastCol_mul_const.solution
