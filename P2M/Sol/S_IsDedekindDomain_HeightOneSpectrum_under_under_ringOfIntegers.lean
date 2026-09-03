import Mathlib
import Definitions.Def_DedekindDomain_Completion_BaseChange
import P2M.Util
namespace P2MW.S_IsDedekindDomain_HeightOneSpectrum_under_under_ringOfIntegers

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxSynthPendingDepth 3
open IsDedekindDomain NumberField

set_option maxHeartbeats 800000

theorem solution
    (K K' K'' : Type) [Field K] [NumberField K] [Field K'] [NumberField K'] [Field K''] [NumberField K'']
    [Algebra K K'] [Algebra K' K''] [Algebra K K''] [IsScalarTower K K' K'']
    (w'' : HeightOneSpectrum (𝓞 K'')) :
    HeightOneSpectrum.under (𝓞 K) (HeightOneSpectrum.under (𝓞 K') w'') = HeightOneSpectrum.under (𝓞 K) w'' := by
  apply HeightOneSpectrum.ext
  show Ideal.comap (algebraMap (𝓞 K) (𝓞 K')) (Ideal.comap (algebraMap (𝓞 K') (𝓞 K'')) w''.asIdeal) =
    Ideal.comap (algebraMap (𝓞 K) (𝓞 K'')) w''.asIdeal
  rw [Ideal.comap_comap, ← IsScalarTower.algebraMap_eq]
