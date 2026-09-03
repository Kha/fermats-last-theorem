import Mathlib
import Definitions.Def_DedekindDomain_Completion_BaseChange
import P2M.Util
import P2M.Sol.S_IsDedekindDomain_HeightOneSpectrum_under_under_ringOfIntegers

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxSynthPendingDepth 3
open IsDedekindDomain NumberField

theorem IsDedekindDomain.HeightOneSpectrum.under_under_ringOfIntegers
    (K K' K'' : Type) [Field K] [NumberField K] [Field K'] [NumberField K'] [Field K''] [NumberField K'']
    [Algebra K K'] [Algebra K' K''] [Algebra K K''] [IsScalarTower K K' K'']
    (w'' : HeightOneSpectrum (𝓞 K'')) :
    HeightOneSpectrum.under (𝓞 K) (HeightOneSpectrum.under (𝓞 K') w'') = HeightOneSpectrum.under (𝓞 K) w'' := by p2m_exact_reverting @_root_.P2MW.S_IsDedekindDomain_HeightOneSpectrum_under_under_ringOfIntegers.solution
