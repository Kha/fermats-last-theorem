import Mathlib
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_NumberField_IdeleBox
import P2M.Util
import P2M.Sol.S_NumberField_AdeleRing_principalIdeles_sup_ideleBox_eq_top

set_option autoImplicit false
theorem NumberField.AdeleRing.principalIdeles_sup_ideleBox_eq_top
    (E : Type*) [Field E] [NumberField E]
    (S S' : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E))) (hSS' : S ⊆ S')
    (hS : M4aHerbrand.principalIdeles (NumberField.RingOfIntegers E) E ⊔
      NumberField.AdeleRing.unitIdelesOutside (NumberField.RingOfIntegers E) E ↑S = ⊤)
    (H : (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E)) → Subgroup (v.adicCompletion E)ˣ)
    (hH : ∀ v ∈ S, H v = ⊤)
    (hsurj : ∀ x : (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E)) → (v.adicCompletion E)ˣ,
      (∀ v ∈ S', v ∉ S → Valued.v ((x v : (v.adicCompletion E)ˣ) : v.adicCompletion E) = 1) →
      ∃ s : Eˣ, (∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E), v ∉ S →
          v.valuation E (s : E) = 1) ∧
        ∀ v ∈ S', v ∉ S →
          x v * (Units.map (algebraMap E (v.adicCompletion E) : E →* v.adicCompletion E) s)⁻¹ ∈ H v) :
    M4aHerbrand.principalIdeles (NumberField.RingOfIntegers E) E ⊔
      NumberField.AdeleRing.ideleBox (NumberField.RingOfIntegers E) E ↑S' H ⊤ = ⊤ := by p2m_exact_reverting @_root_.P2MW.S_NumberField_AdeleRing_principalIdeles_sup_ideleBox_eq_top.solution
