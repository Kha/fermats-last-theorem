import Definitions.Def_LanglandsTunnell_CubicInduction_KFinite3
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_finiteDimensional_invariants_gKSpan_of_isCentreFinite

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm
open scoped LanglandsTunnell.CubicInduction.WhittakerBlock in

theorem
LanglandsTunnell.CubicInduction.finiteDimensional_invariants_gKSpan_of_isCentreFinite
    (f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hfin : WhittakerBlock.IsOrthFinite f)
    (hcentre : ∀ φ ∈ WhittakerBlock.orthSpan f, WhittakerBlock.IsCentreFinite φ)
    (hrot : ∀ i j : Fin 3, ∀ φ : WhittakerBlock.smoothFunctions3,
      (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) ∈ WhittakerBlock.orthSpan f →
        WhittakerBlock.derivAction3 (Matrix.single i j (1 : ℂ) - Matrix.single j i 1) φ = 0)
    (B : WhittakerBlock.smoothFunctions3 → WhittakerBlock.smoothFunctions3 → ℂ)
    (hlin : ∀ (z : ℂ), ∀ w₁ ∈ WhittakerBlock.gKSpan f, ∀ w₂ ∈ WhittakerBlock.gKSpan f, ∀ w' ∈ WhittakerBlock.gKSpan f,
      B (z • w₁ + w₂) w' = z * B w₁ w' + B w₂ w')
    (hsymm : ∀ w ∈ WhittakerBlock.gKSpan f, ∀ w' ∈ WhittakerBlock.gKSpan f, B w' w = (starRingEnd ℂ) (B w w'))
    (hpos : ∀ w ∈ WhittakerBlock.gKSpan f, w ≠ 0 → 0 < (B w w).re)
    (hskew : ∀ i j : Fin 3, ∀ x ∈ WhittakerBlock.gKSpan f, ∀ y ∈ WhittakerBlock.gKSpan f,
      B (WhittakerBlock.derivAction3 (Matrix.single i j (1 : ℂ) - Matrix.single j i 1) x) y =
        -B x (WhittakerBlock.derivAction3 (Matrix.single i j (1 : ℂ) - Matrix.single j i 1) y)) :
    FiniteDimensional ℂ ↥((WhittakerBlock.gKSpan f).restrictScalars ℂ ⊓
      ⨅ i : Fin 3, ⨅ j : Fin 3,
        LinearMap.ker (WhittakerBlock.derivAction3 (Matrix.single i j (1 : ℂ) - Matrix.single j i 1))) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_finiteDimensional_invariants_gKSpan_of_isCentreFinite.solution
