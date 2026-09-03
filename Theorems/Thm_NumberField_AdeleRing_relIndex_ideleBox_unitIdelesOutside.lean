import Mathlib
import Definitions.Def_NumberField_IdeleBox
import P2M.Util
import P2M.Sol.S_NumberField_AdeleRing_relIndex_ideleBox_unitIdelesOutside

set_option autoImplicit false
theorem NumberField.AdeleRing.relIndex_ideleBox_unitIdelesOutside
    (R : Type*) [CommRing R] [IsDedekindDomain R] (K : Type*) [Field K] [NumberField K] [Algebra R K]
    [IsFractionRing R K] (S : Finset (IsDedekindDomain.HeightOneSpectrum R))
    (H : (v : IsDedekindDomain.HeightOneSpectrum R) → Subgroup (v.adicCompletion K)ˣ)
    (Hinf : (w : NumberField.InfinitePlace K) → Subgroup (w.Completion)ˣ) :
    (NumberField.AdeleRing.ideleBox R K (↑S) H Hinf).relIndex (NumberField.AdeleRing.unitIdelesOutside R K (↑S))
      = (∏ v ∈ S, (H v).index) * ∏ w : NumberField.InfinitePlace K, (Hinf w).index := by p2m_exact_reverting @_root_.P2MW.S_NumberField_AdeleRing_relIndex_ideleBox_unitIdelesOutside.solution
