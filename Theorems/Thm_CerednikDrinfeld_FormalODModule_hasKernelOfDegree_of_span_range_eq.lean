import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_FormalODModule_hasKernelOfDegree_of_span_range_eq

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal

theorem CerednikDrinfeld.FormalODModule.hasKernelOfDegree_of_span_range_eq
    (p : ℕ) [Fact p.Prime] {B : Type} [CommRing B]
    (u : Series B) (I : Ideal (MvPowerSeries (Fin 2) B)) (h : ℕ)
    (huI : Ideal.span (Set.range u) = I)
    (hfin : Module.Finite B (MvPowerSeries (Fin 2) B ⧸ I))
    (hproj : Module.Projective B (MvPowerSeries (Fin 2) B ⧸ I))
    (hrank : ∀ (κ : Type) [Field κ] (f : B →+* κ),
      Module.finrank κ (MvPowerSeries (Fin 2) κ ⧸ I.map (MvPowerSeries.map f)) = p ^ h) :
    FormalODModule.HasKernelOfDegree u (p ^ h) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_FormalODModule_hasKernelOfDegree_of_span_range_eq.solution
