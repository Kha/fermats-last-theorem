import Definitions.Def_AutomorphicForm_CuspidalSpectrumSubrep
import P2M.Util
import P2M.Sol.S_AutomorphicForm_CuspidalSpectrum_exists_isArchBiFinite_flat

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open IsDedekindDomain AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent AutomorphicForm.CuspidalSpectrum
open scoped InnerProductSpace

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

theorem AutomorphicForm.CuspidalSpectrum.exists_isArchBiFinite_flat
    (F : Type) [Field F] [NumberField F] (σ : ℝ) (tys : ArchTypeFamily F)
    (f : AdelicGL2 (𝓞 F) F → ℂ) (hf : IsFactorizableTestFn F f) (hft : IsArchBiFinite F tys f) :
    ∃ tys' : ArchTypeFamily F, IsArchBiFinite F tys' (flat F σ f) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_CuspidalSpectrum_exists_isArchBiFinite_flat.solution
