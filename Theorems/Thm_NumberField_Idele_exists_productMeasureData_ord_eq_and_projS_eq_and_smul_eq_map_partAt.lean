import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_UnramifiedWhittaker_ZetaIntegrand
import P2M.Util
import P2M.Sol.S_NumberField_Idele_exists_productMeasureData_ord_eq_and_projS_eq_and_smul_eq_map_partAt

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain

theorem NumberField.Idele.exists_productMeasureData_ord_eq_and_projS_eq_and_smul_eq_map_partAt
    (K : Type) [Field K] [NumberField K]
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
    (SK : Finset (HeightOneSpectrum (𝓞 K)))
    (νZK : Measure (AdeleRing (𝓞 K) K)ˣ) [νZK.IsHaarMeasure] :
    ∃ PZ : UnramifiedWhittaker.ProductMeasureData SK νZK,
      PZ.ord = NumberField.Idele.ord K ∧
      PZ.projS = NumberField.Idele.partAt K SK ∧
      ENNReal.ofReal PZ.c • PZ.νS = Measure.map (NumberField.Idele.partAt K SK)
        (νZK.restrict (NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K ↑SK)) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_Idele_exists_productMeasureData_ord_eq_and_projS_eq_and_smul_eq_map_partAt.solution
