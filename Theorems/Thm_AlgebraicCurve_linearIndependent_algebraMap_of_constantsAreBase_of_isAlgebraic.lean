import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_AdelicIndex
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_linearIndependent_algebraMap_of_constantsAreBase_of_isAlgebraic

open AlgebraicCurve
open scoped TensorProduct

theorem AlgebraicCurve.linearIndependent_algebraMap_of_constantsAreBase_of_isAlgebraic
    (K F K' F' : Type*)
    [Field K] [Field F] [Field K'] [Field F'] [Algebra K F] [Algebra K' F']
    [Algebra K K'] [Algebra F F'] [Algebra K F'] [IsScalarTower K K' F'] [IsScalarTower K F F']
    [PerfectField K] [Algebra.IsAlgebraic K K']
    (hC : AlgebraicCurve.ConstantsAreBase K F)
    {ι : Type*} {b : ι → F} (hb : LinearIndependent K b) :
    LinearIndependent K' (fun i => algebraMap F F' (b i)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_linearIndependent_algebraMap_of_constantsAreBase_of_isAlgebraic.solution
