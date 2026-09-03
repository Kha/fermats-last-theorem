import Mathlib
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadrupleRelations
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_FormalOmega_exists_forall_pointUnder_eq_and_isOpen_setOf_mem_of_span_eq_top

set_option autoImplicit false

open scoped TensorProduct
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem CerednikDrinfeld.FormalOmega.exists_forall_pointUnder_eq_and_isOpen_setOf_mem_of_span_eq_top
    {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K]
    {B : Type} [CommRing B] [Algebra 𝒪 B] {k : ℕ} (f : Fin k → B) (hf : Ideal.span (Set.range f) = ⊤)
    (N : ∀ i : Fin k, PrimeSpectrum (Localization.Away (f i)) → Submodule 𝒪 (Fin 2 → K))
    (hN : ∀ (i : Fin k) (v : Fin 2 → K), IsOpen {y : PrimeSpectrum (Localization.Away (f i)) | v ∈ N i y})
    (hcompat : ∀ (i j : Fin k) (y : PrimeSpectrum (Localization.Away (f i))) (z : PrimeSpectrum (Localization.Away (f j))),
      DrinfeldDatum.pointUnder (IsScalarTower.toAlgHom 𝒪 B (Localization.Away (f i))) y =
        DrinfeldDatum.pointUnder (IsScalarTower.toAlgHom 𝒪 B (Localization.Away (f j))) z → N i y = N j z) :
    ∃ Ng : PrimeSpectrum B → Submodule 𝒪 (Fin 2 → K),
      (∀ (i : Fin k) (y : PrimeSpectrum (Localization.Away (f i))),
          Ng (DrinfeldDatum.pointUnder (IsScalarTower.toAlgHom 𝒪 B (Localization.Away (f i))) y) = N i y) ∧
      ∀ v : Fin 2 → K, IsOpen {x : PrimeSpectrum B | v ∈ Ng x} := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_FormalOmega_exists_forall_pointUnder_eq_and_isOpen_setOf_mem_of_span_eq_top.solution
