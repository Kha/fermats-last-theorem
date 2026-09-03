import Definitions.Def_RepTheory_LevelDensity
import Definitions.Def_RepTheory_TestFunctionActionHom
import P2M.Util
import P2M.Sol.S_TestFunctionAction_isLevelDenseAction_heckeSmul

set_option autoImplicit false

open MeasureTheory
open FLT.SmoothAdmissibleSchurCommutant SchwartzBruhatSpace TestFunctionAction

theorem TestFunctionAction.isLevelDenseAction_heckeSmul
    {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G]
    {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : G →* Module.End ℂ V) (hsm : IsSmoothRep π)
    (μ : Measure G) [μ.IsHaarMeasure]
    (hirr : IsIrreducibleRep π) (hadm : IsAdmissibleRep π) :
    TwistedPairing.IsLevelDenseAction π (heckeSmulHom π hsm μ) := by p2m_exact_reverting @_root_.P2MW.S_TestFunctionAction_isLevelDenseAction_heckeSmul.solution
