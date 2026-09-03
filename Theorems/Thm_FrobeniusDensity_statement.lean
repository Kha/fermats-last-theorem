import Definitions.Def_TaylorWiles_Primes
import P2M.Util
import P2M.Sol.S_FrobeniusDensity_statement
attribute [-instance] FrobeniusDensity.liesOver_ratBelow

open NumberField
theorem FrobeniusDensity.statement (L : Type*) [Field L] [NumberField L] [IsGalois ℚ L] :
    FrobeniusDensity.Statement L := by p2m_exact_reverting @_root_.P2MW.S_FrobeniusDensity_statement.solution
