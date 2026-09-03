import Mathlib
import P2M.Util
import P2M.Sol.S_ValuationSubring_exists_ringEquiv_comap_of_range_eq_inter

set_option autoImplicit false

theorem ValuationSubring.exists_ringEquiv_comap_of_range_eq_inter
    {F L : Type*} [Field F] [Field L] [Algebra F L]
    (k₀ : IntermediateField F L) (A : ValuationSubring L)
    (A₀ : Type*) [CommRing A₀] (ι : A₀ →+* ↥A) (hι : Function.Injective ι)
    (hιK₀ : Set.range (fun a : A₀ => ((ι a : ↥A) : L)) = (A : Set L) ∩ (k₀ : Set L)) :
    ∃ e : A₀ ≃+* ↥(A.comap (algebraMap ↥k₀ L)),
      ∀ a : A₀, algebraMap ↥k₀ L ((e a : ↥(A.comap (algebraMap ↥k₀ L))) : ↥k₀) = ((ι a : ↥A) : L) := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_exists_ringEquiv_comap_of_range_eq_inter.solution
