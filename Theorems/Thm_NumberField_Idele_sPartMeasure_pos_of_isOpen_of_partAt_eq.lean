import Definitions.Def_NumberField_IdeleProductMeasure
import P2M.Util
import P2M.Sol.S_NumberField_Idele_sPartMeasure_pos_of_isOpen_of_partAt_eq

set_option autoImplicit false

open MeasureTheory NumberField NumberField.Idele IsDedekindDomain
open scoped ENNReal

theorem NumberField.Idele.sPartMeasure_pos_of_isOpen_of_partAt_eq
    (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (t₀ : (AdeleRing (𝓞 F) F)ˣ)
    (ht₀ : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S → ((t₀ : AdeleRing (𝓞 F) F)).2 v = 1)
    (U : Set (AdeleRing (𝓞 F) F)ˣ) (hU : IsOpen U) (hU₀ : t₀ ∈ U) :
    0 < sPartMeasure F S U := by p2m_exact_reverting @_root_.P2MW.S_NumberField_Idele_sPartMeasure_pos_of_isOpen_of_partAt_eq.solution
