import Definitions.Def_FrobeniusDensity_DegOneAsymptotic
import P2M.Util
import P2M.Sol.S_FrobeniusDensity_degOneAsymptotic
attribute [-instance] FrobeniusDensity.liesOver_ratBelow

open NumberField
theorem FrobeniusDensity.degOneAsymptotic (L : Type*) [Field L] [NumberField L] [IsGalois ℚ L] :
    FrobeniusDensity.DegOneAsymptotic L := by p2m_exact_reverting @_root_.P2MW.S_FrobeniusDensity_degOneAsymptotic.solution
