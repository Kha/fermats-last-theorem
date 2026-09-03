import Definitions.Def_FrobeniusDensity_DegOneAsymptotic
import P2M.Util
import P2M.Sol.S_FrobeniusDensity_statement_of_degOneAsymptotic

open NumberField
theorem FrobeniusDensity.statement_of_degOneAsymptotic (L : Type*) [Field L] [NumberField L]
    [IsGalois ℚ L] (hL : FrobeniusDensity.DegOneAsymptotic L) :
    FrobeniusDensity.Statement L := by p2m_exact_reverting @_root_.P2MW.S_FrobeniusDensity_statement_of_degOneAsymptotic.solution
