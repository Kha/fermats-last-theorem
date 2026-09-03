import Definitions.Def_FrobeniusDensity_DegOneAsymptotic
import Theorems.Thm_FrobeniusDensity_degOneAsymptotic
import Theorems.Thm_FrobeniusDensity_statement_of_degOneAsymptotic
import P2M.Util
namespace P2MW.S_FrobeniusDensity_statement
attribute [-instance] FrobeniusDensity.liesOver_ratBelow

open NumberField

theorem solution (L : Type*) [Field L] [NumberField L] [IsGalois ℚ L] :
    FrobeniusDensity.Statement L :=
  FrobeniusDensity.statement_of_degOneAsymptotic L (FrobeniusDensity.degOneAsymptotic L)
