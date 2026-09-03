import Definitions.Def_LanglandsTunnell_CubicInduction_GodementSection
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_isSchwartzBruhat_and_law_matFourier23_dualDatum

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory AutomorphicForm LanglandsTunnell.TateLocal
  LanglandsTunnell.CubicInduction NumberField.StandardAddChar

theorem LanglandsTunnell.CubicInduction.isSchwartzBruhat_and_law_matFourier23_dualDatum
    (v : HeightOneSpectrum (𝓞 ℚ)) (η : AddChar (v.adicCompletion ℚ) ℂ) (n : ℤ)
    (hηn : ∀ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp n → η x = 1)
    (hηn' : ∃ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp (n + 1) ∧ η x ≠ 1)
    (w₂ : GL (Fin 2) (v.adicCompletion ℚ))
    (hw₂ : ((w₂ : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) = !![0, 1; 1, 0])
    (Φ : Matrix (Fin 2) (Fin 3) (v.adicCompletion ℚ) → GL (Fin 2) (v.adicCompletion ℚ) → ℂ)
    (hΦ : ∃ (m : ℕ) (φ : Fin m → Matrix (Fin 2) (Fin 3) (v.adicCompletion ℚ) → ℂ)
        (K : Fin m → GL (Fin 2) (v.adicCompletion ℚ) → ℂ),
        (∀ i, IsLocallyConstant (φ i) ∧ HasCompactSupport (φ i)) ∧
        (∀ i, IsLocallyConstant (K i) ∧
          ∀ (a : v.adicCompletion ℚ) (k : GL (Fin 2) (v.adicCompletion ℚ)), K i (unipotentGL2 a * k) = η a * K i k) ∧
        Φ = fun X k => ∑ i, φ i X * K i k) :
    (∀ k : GL (Fin 2) (v.adicCompletion ℚ),
        IsSchwartzBruhat (fun X : Matrix (Fin 2) (Fin 3) (v.adicCompletion ℚ) =>
          matFourier23 v η⁻¹ (fun Y => Φ Y (w₂ * transposeInvN (Fin 2) k)) X)) ∧
    ∀ (X : Matrix (Fin 2) (Fin 3) (v.adicCompletion ℚ)) (a : v.adicCompletion ℚ)
      (k : GL (Fin 2) (v.adicCompletion ℚ)),
      matFourier23 v η⁻¹ (fun Y => Φ Y (w₂ * transposeInvN (Fin 2) (unipotentGL2 a * k))) X =
        η⁻¹ a * matFourier23 v η⁻¹ (fun Y => Φ Y (w₂ * transposeInvN (Fin 2) k)) X := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_isSchwartzBruhat_and_law_matFourier23_dualDatum.solution
