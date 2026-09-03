import Definitions.Def_FrobeniusDensity_PrimeSums
import Mathlib.NumberTheory.NumberField.DedekindZeta
import P2M.Util
import P2M.Sol.S_FrobeniusDensity_tendsto_sub_one_mul_idealSum_test

open NumberField
theorem FrobeniusDensity.tendsto_sub_one_mul_idealSum_test
    (K : Type*) [Field K] [NumberField K] :
    Filter.Tendsto (fun s : ℝ => (s - 1) * (FrobeniusDensity.idealSum K s).toReal)
      (nhdsWithin 1 (Set.Ioi 1)) (nhds (dedekindZeta_residue K)) := by p2m_exact_reverting @_root_.P2MW.S_FrobeniusDensity_tendsto_sub_one_mul_idealSum_test.solution
