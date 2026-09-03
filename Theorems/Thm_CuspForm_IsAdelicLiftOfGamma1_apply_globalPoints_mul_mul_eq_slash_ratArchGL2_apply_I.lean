import Definitions.Def_CuspForm_PrimitiveFormGamma1
import Definitions.Def_CuspForm_AdelicLiftGamma1
import Definitions.Def_CuspForm_AdelicLift
import Definitions.Def_CuspForm_Newforms
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import P2M.Util
import P2M.Sol.S_CuspForm_IsAdelicLiftOfGamma1_apply_globalPoints_mul_mul_eq_slash_ratArchGL2_apply_I

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open scoped ModularForm

theorem CuspForm.IsAdelicLiftOfGamma1.apply_globalPoints_mul_mul_eq_slash_ratArchGL2_apply_I
    {M : ℕ} [NeZero M] {h : CuspForm (CongruenceSubgroup.Gamma1 M) 2}
    {Φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ} (hΦ : CuspForm.IsAdelicLiftOfGamma1 h Φ)
    (γ : GL (Fin 2) ℚ) (x u : AdelicGL2 (𝓞 ℚ) ℚ)
    (hu : u ∈ (productionPinsGeneral ℚ).U (AdelicDock.ratLevel M))
    (hx : glFin (𝓞 ℚ) ℚ x = 1) (hpos : LanglandsTunnell.ratArchGL2 x ∈ Matrix.GLPos (Fin 2) ℝ) :
    Φ (globalPoints (𝓞 ℚ) ℚ γ * x * u) =
      ((⇑h) ∣[(2 : ℤ)] LanglandsTunnell.ratArchGL2 x) UpperHalfPlane.I := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_IsAdelicLiftOfGamma1_apply_globalPoints_mul_mul_eq_slash_ratArchGL2_apply_I.solution
