import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetVector3
import Definitions.Def_AutomorphicForm_ArchWeightChar
import Definitions.Def_LanglandsTunnell_ArchBaseChange
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_Converse_exists_forall_integrable_dualQuadruple_and_torusTriple_detPow_blockQuadratic_colHarmonic_of_evenSheet

set_option autoImplicit false

open NumberField AutomorphicForm LanglandsTunnell LanglandsTunnell.Converse MeasureTheory

theorem LanglandsTunnell.Converse.exists_forall_integrable_dualQuadruple_and_torusTriple_detPow_blockQuadratic_colHarmonic_of_evenSheet
    (ν₁ ν₂ : ℂ) (b : ZMod 2)
    (W : ℝ → ℂ) (hWc : ContinuousOn W {t : ℝ | t ≠ 0})
    (hWpar : ∀ t : ℝ, W (-t) = (-1 : ℂ) ^ b.val * W t)
    (hW : ∀ t : ℝ, 0 < t →
      W t + (-1 : ℂ) ^ b.val * W (-t) =
        (t : ℂ) * ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ (ν₁ + signShift (b + b)) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              ((((t) / r : ℝ) : ℂ) ^ (ν₂ + signShift (b + b)) * (Real.exp (-(Real.pi * ((t) / r) ^ 2)) : ℂ)) / (r : ℂ)))
    {P₂ : RealArchParam} (D : ArchDatumR P₂)
    (a : ℝ) (ha : a ≠ 0) (u₀ cP : ℂ) (a₀ sP : ZMod 2) (n : ℕ) (δ : ℕ) (hδ : δ = 0 ∨ δ = 1) :
    ∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
      Integrable (fun r : ℝ × ℝ × ℝ × ℝ =>
        (((r.1 : ℝ) : ℂ) ^ (2 * s - cP - P₂.centralExponent + n) * (Real.exp (-(Real.pi * r.1 ^ 2 * r.2.2.1 ^ 2)) : ℂ)) *
        ((ArchR.quasiChar 0 sP (-r.2.1) * ArchR.quasiChar 0 a₀ (-r.2.1) * ArchR.quasiChar 0 1 r.2.1 * ArchR.quasiChar 0 (n : ZMod 2) r.2.2.1 * ArchR.quasiChar 0 a₀ r.2.2.1) *
          (W (-r.2.1) * (((((r.2.2.2 : ℝ) : ℂ) * ArchR.quasiChar 0 1 r.2.1) * ((a : ℂ) ^ 2 * ArchR.quasiChar 0 1 r.2.1 * (((r.2.2.2 * r.2.2.1)⁻¹ : ℝ) : ℂ)) ^ δ) *
              (-(((r.2.1 : ℝ) : ℂ) ^ 2 * ((r.2.2.2 : ℝ) : ℂ) ^ 2) + (a : ℂ) ^ 2 * ((r.2.2.2⁻¹ : ℝ) : ℂ) ^ 2 + 1 / (2 * (Real.pi : ℂ)) - (a : ℂ) ^ 2 * ((r.2.2.1⁻¹ : ℝ) : ℂ) ^ 2 + 2 * (a : ℂ) * ((|r.2.1| : ℝ) : ℂ) * ((r.2.2.2 : ℝ) : ℂ) * ((r.2.2.1⁻¹ : ℝ) : ℂ))) * D.W (ArchR.diagOne (a * |r.2.1| * r.2.2.2 / r.2.2.1))) *
          ((((|r.2.1| : ℝ) : ℂ) ^ (s - 5 / 2 - cP - P₂.centralExponent)) * (((|r.2.2.1| : ℝ) : ℂ) ^ (u₀ + n)) *
            (((r.2.2.2 : ℝ) : ℂ) ^ (u₀ - P₂.centralExponent - 3))) *
          ((Real.exp (-(Real.pi * r.2.1 ^ 2 * r.2.2.2 ^ 2)) : ℂ) * (Real.exp (-(Real.pi * a ^ 2 / r.2.2.2 ^ 2)) : ℂ) * (Real.exp (-(Real.pi * a ^ 2 / r.2.2.1 ^ 2)) : ℂ)))) (((volume : Measure ℝ).restrict (Set.Ioi 0)).prod ((volume : Measure ℝ).prod ((volume : Measure ℝ).prod ((volume : Measure ℝ).restrict (Set.Ioi 0))))) ∧
      ∀ b₀ b₁ b₂ b₃ b₄ : ℂ, Integrable (fun q : ℝ × ℝ × ℝ =>
        (ArchR.quasiChar 0 sP (-q.1) * ArchR.quasiChar 0 a₀ (-q.1) * ArchR.quasiChar 0 1 q.1 * ArchR.quasiChar 0 (n : ZMod 2) q.2.1 * ArchR.quasiChar 0 a₀ q.2.1) *
          (W (-q.1) * (((((q.2.2 : ℝ) : ℂ) * ArchR.quasiChar 0 1 q.1) * ((a : ℂ) ^ 2 * ArchR.quasiChar 0 1 q.1 * (((q.2.2 * q.2.1)⁻¹ : ℝ) : ℂ)) ^ δ) *
              (b₀ * (((q.1 : ℝ) : ℂ) ^ 2 * ((q.2.2 : ℝ) : ℂ) ^ 2) + b₁ * ((a : ℂ) ^ 2 * ((q.2.2⁻¹ : ℝ) : ℂ) ^ 2) + b₂ + b₃ * ((a : ℂ) ^ 2 * ((q.2.1⁻¹ : ℝ) : ℂ) ^ 2) + b₄ * ((a : ℂ) * ((|q.1| : ℝ) : ℂ) * ((q.2.2 : ℝ) : ℂ) * ((q.2.1⁻¹ : ℝ) : ℂ)))) * D.W (ArchR.diagOne (a * |q.1| * q.2.2 / q.2.1))) *
          ((((|q.1| : ℝ) : ℂ) ^ (s - 5 / 2 - cP - P₂.centralExponent)) * (((|q.2.1| : ℝ) : ℂ) ^ (u₀ + cP + P₂.centralExponent - 2 * s - 1)) *
            (((q.2.2 : ℝ) : ℂ) ^ (u₀ - P₂.centralExponent - 3))) *
          ((Real.exp (-(Real.pi * q.1 ^ 2 * q.2.2 ^ 2)) : ℂ) * (Real.exp (-(Real.pi * a ^ 2 / q.2.2 ^ 2)) : ℂ) * (Real.exp (-(Real.pi * a ^ 2 / q.2.1 ^ 2)) : ℂ))) ((volume : Measure ℝ).prod ((volume : Measure ℝ).prod ((volume : Measure ℝ).restrict (Set.Ioi 0)))) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_Converse_exists_forall_integrable_dualQuadruple_and_torusTriple_detPow_blockQuadratic_colHarmonic_of_evenSheet.solution
