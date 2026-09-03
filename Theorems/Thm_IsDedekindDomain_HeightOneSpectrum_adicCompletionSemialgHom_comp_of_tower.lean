import Mathlib
import Definitions.Def_DedekindDomain_Completion_BaseChange
import P2M.Util
import P2M.Sol.S_IsDedekindDomain_HeightOneSpectrum_adicCompletionSemialgHom_comp_of_tower

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxSynthPendingDepth 3
open IsDedekindDomain NumberField

theorem IsDedekindDomain.HeightOneSpectrum.adicCompletionSemialgHom_comp_of_tower
    (K K' K'' : Type) [Field K] [NumberField K] [Field K'] [NumberField K'] [Field K''] [NumberField K'']
    [Algebra K K'] [Algebra K' K''] [Algebra K K''] [IsScalarTower K K' K'']
    (w'' : HeightOneSpectrum (𝓞 K''))
    (h : HeightOneSpectrum.under (𝓞 K) w'' = HeightOneSpectrum.under (𝓞 K) (HeightOneSpectrum.under (𝓞 K') w''))
    (x : (HeightOneSpectrum.under (𝓞 K) (HeightOneSpectrum.under (𝓞 K') w'')).adicCompletion K) :
    HeightOneSpectrum.Extension.adicCompletionSemialgHom K' K''
        (⟨w'', rfl⟩ : (HeightOneSpectrum.under (𝓞 K') w'').Extension (𝓞 K''))
      (HeightOneSpectrum.Extension.adicCompletionSemialgHom K K'
        (⟨HeightOneSpectrum.under (𝓞 K') w'', rfl⟩ :
          (HeightOneSpectrum.under (𝓞 K) (HeightOneSpectrum.under (𝓞 K') w'')).Extension (𝓞 K')) x) =
    HeightOneSpectrum.Extension.adicCompletionSemialgHom K K''
        (⟨w'', h⟩ : (HeightOneSpectrum.under (𝓞 K) (HeightOneSpectrum.under (𝓞 K') w'')).Extension (𝓞 K'')) x := by p2m_exact_reverting @_root_.P2MW.S_IsDedekindDomain_HeightOneSpectrum_adicCompletionSemialgHom_comp_of_tower.solution
