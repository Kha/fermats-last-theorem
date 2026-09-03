import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import P2M.Util
import P2M.Sol.S_AutomorphicForm_isRegularSemisimple_finComponent_glFin_centralScalar_mul_diagUnits2_of_ne_one

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicHaar IsDedekindDomain

attribute [local instance] NumberField.AdelicHaar.glBorel AutomorphicForm.centralizerBorel

open LanglandsTunnell.CubicInduction (diagUnits2)

theorem AutomorphicForm.isRegularSemisimple_finComponent_glFin_centralScalar_mul_diagUnits2_of_ne_one (K : Type) [Field K] [NumberField K]
    (u : Kˣ) (hu : (u : K) ≠ 1) (z : (AdeleRing (𝓞 K) K)ˣ) (v : HeightOneSpectrum (𝓞 K)) :
    AutomorphicForm.IsRegularSemisimple (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_isRegularSemisimple_finComponent_glFin_centralScalar_mul_diagUnits2_of_ne_one.solution
