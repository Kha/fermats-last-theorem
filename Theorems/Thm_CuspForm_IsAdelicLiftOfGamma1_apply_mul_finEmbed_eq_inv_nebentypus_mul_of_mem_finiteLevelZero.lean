import Definitions.Def_CuspForm_PrimitiveFormGamma1
import Definitions.Def_CuspForm_AdelicLiftGamma1
import Definitions.Def_CuspForm_AdelicLift
import Definitions.Def_CuspForm_Newforms
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import P2M.Util
import P2M.Sol.S_CuspForm_IsAdelicLiftOfGamma1_apply_mul_finEmbed_eq_inv_nebentypus_mul_of_mem_finiteLevelZero

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open scoped ModularForm

theorem CuspForm.IsAdelicLiftOfGamma1.apply_mul_finEmbed_eq_inv_nebentypus_mul_of_mem_finiteLevelZero
    {M : ℕ} [NeZero M] {ε : DirichletCharacter ℂ M} {h : CuspForm (CongruenceSubgroup.Gamma1 M) 2}
    (hε : CuspForm.HasNebentypus ε h)
    {Φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ} (hΦ : CuspForm.IsAdelicLiftOfGamma1 h Φ)
    (u : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) (hu : u ∈ finiteLevelZero (𝓞 ℚ) ℚ (AdelicDock.ratLevel M))
    (d : ℤ)
    (hd : (u : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) 1 1
        - algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (d : ℚ) ∈ idealBall (𝓞 ℚ) ℚ (AdelicDock.ratLevel M))
    (x : AdelicGL2 (𝓞 ℚ) ℚ) :
    Φ (x * AdelicDock.finEmbed (𝓞 ℚ) ℚ u) = (ε (d : ZMod M))⁻¹ * Φ x := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_IsAdelicLiftOfGamma1_apply_mul_finEmbed_eq_inv_nebentypus_mul_of_mem_finiteLevelZero.solution
