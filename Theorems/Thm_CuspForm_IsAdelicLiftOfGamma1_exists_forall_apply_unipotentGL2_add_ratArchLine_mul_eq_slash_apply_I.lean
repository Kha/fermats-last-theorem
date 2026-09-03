import Definitions.Def_CuspForm_PrimitiveFormGamma1
import Definitions.Def_CuspForm_AdelicLiftGamma1
import Definitions.Def_CuspForm_AdelicLift
import Definitions.Def_CuspForm_Newforms
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_NumberField_AdelicTraceProducer
import P2M.Util
import P2M.Sol.S_CuspForm_IsAdelicLiftOfGamma1_exists_forall_apply_unipotentGL2_add_ratArchLine_mul_eq_slash_apply_I

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox NumberField.StandardAddChar
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open scoped ModularForm MatrixGroups

theorem CuspForm.IsAdelicLiftOfGamma1.exists_forall_apply_unipotentGL2_add_ratArchLine_mul_eq_slash_apply_I
    {M : ℕ} [NeZero M] {h : CuspForm (CongruenceSubgroup.Gamma1 M) 2}
    {Φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ} (hΦ : CuspForm.IsAdelicLiftOfGamma1 h Φ)
    (x : AdeleRing (𝓞 ℚ) ℚ) (hx : x.2 ∈ NumberField.AdelicBox.integralFiniteAdeles (𝓞 ℚ) ℚ)
    (h₁ q : AdelicGL2 (𝓞 ℚ) ℚ) (hh₁ : glFin (𝓞 ℚ) ℚ h₁ = 1)
    (hpos : LanglandsTunnell.ratArchGL2 h₁ ∈ Matrix.GLPos (Fin 2) ℝ)
    (hq : glArch (𝓞 ℚ) ℚ q = 1) (hqint : glFin (𝓞 ℚ) ℚ q ∈ finiteIntegralGL2 (𝓞 ℚ) ℚ) :
    ∃ ρ : SL(2, ℤ), ∀ t : ℝ,
      Φ (unipotentGL2 (R := AdeleRing (𝓞 ℚ) ℚ) (x.1 + ratArchLine t, x.2) * (h₁ * q)) =
        ((⇑h) ∣[(2 : ℤ)] (((ρ : GL (Fin 2) ℝ))⁻¹ *
            LanglandsTunnell.ratArchGL2 (unipotentGL2 (R := AdeleRing (𝓞 ℚ) ℚ) (x.1 + ratArchLine t, x.2) * h₁)))
          UpperHalfPlane.I := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_IsAdelicLiftOfGamma1_exists_forall_apply_unipotentGL2_add_ratArchLine_mul_eq_slash_apply_I.solution
