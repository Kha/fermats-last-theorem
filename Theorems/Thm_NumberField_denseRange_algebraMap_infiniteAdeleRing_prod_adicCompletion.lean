import Mathlib
import P2M.Util
import P2M.Sol.S_NumberField_denseRange_algebraMap_infiniteAdeleRing_prod_adicCompletion

set_option autoImplicit false

open NumberField IsDedekindDomain

theorem NumberField.denseRange_algebraMap_infiniteAdeleRing_prod_adicCompletion
    (K : Type*) [Field K] [NumberField K] (S : Finset (HeightOneSpectrum (𝓞 K))) :
    DenseRange fun x : K =>
      (algebraMap K (InfiniteAdeleRing K) x, fun v : ↥S => algebraMap K (v.1.adicCompletion K) x) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_denseRange_algebraMap_infiniteAdeleRing_prod_adicCompletion.solution
