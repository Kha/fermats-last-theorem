import Mathlib
import Definitions.Def_IsDedekindDomain_FiniteUnitIdeles
import Definitions.Def_IsDedekindDomain_FiniteUnitIdelesOutside
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import P2M.Util
import P2M.Sol.S_NumberField_AdeleRing_principalIdeles_sup_unitIdelesOutside_eq_top

set_option autoImplicit false
open scoped nonZeroDivisors
theorem NumberField.AdeleRing.principalIdeles_sup_unitIdelesOutside_eq_top
    (R : Type*) [CommRing R] [IsDedekindDomain R] (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
    (S : Set (IsDedekindDomain.HeightOneSpectrum R))
    (hS : ∀ c : ClassGroup R, ∃ I : (Ideal R)⁰, ClassGroup.mk0 I = c ∧
      ∀ v : IsDedekindDomain.HeightOneSpectrum R, v.asIdeal ∣ (I : Ideal R) → v ∈ S) :
    M4aHerbrand.principalIdeles R K ⊔ NumberField.AdeleRing.unitIdelesOutside R K S = ⊤ := by p2m_exact_reverting @_root_.P2MW.S_NumberField_AdeleRing_principalIdeles_sup_unitIdelesOutside_eq_top.solution
