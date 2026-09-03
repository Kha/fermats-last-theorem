import Mathlib
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneChartRings
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_FormalOmega_chartERing_smoothOfRelativeDimension_one_specMap_quotient_of_mem_minimalPrimes_level_zero

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.FormalOmega AlgebraicGeometry CategoryTheory

theorem CerednikDrinfeld.FormalOmega.chartERing.smoothOfRelativeDimension_one_specMap_quotient_of_mem_minimalPrimes_level_zero
    (𝒪 : Type) [CommRing 𝒪] (π : 𝒪) (r : ℕ) (hπ : (Ideal.span ({π} : Set 𝒪)).IsMaximal)
    (P : Ideal ((chartERing 𝒪 π r) ⧸ (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)})))
    (hP : P ∈ minimalPrimes ((chartERing 𝒪 π r) ⧸ (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)}))) :
    SmoothOfRelativeDimension 1 (Spec.map (CommRingCat.ofHom (R := 𝒪 ⧸ Ideal.span {π ^ (0 + 1)})
      (S := ((chartERing 𝒪 π r) ⧸ (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)})) ⧸ P) ((Ideal.Quotient.mk P).comp
      (Ideal.quotientMap (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)}) (algebraMap 𝒪 (chartERing 𝒪 π r))
        (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr (Ideal.mem_comap.mpr (by rw [map_pow]; exact Ideal.subset_span rfl)))))))) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_FormalOmega_chartERing_smoothOfRelativeDimension_one_specMap_quotient_of_mem_minimalPrimes_level_zero.solution
