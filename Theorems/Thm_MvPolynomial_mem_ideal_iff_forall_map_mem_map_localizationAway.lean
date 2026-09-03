import Mathlib
import P2M.Util
import P2M.Sol.S_MvPolynomial_mem_ideal_iff_forall_map_mem_map_localizationAway

set_option autoImplicit false
open MvPolynomial

theorem MvPolynomial.mem_ideal_iff_forall_map_mem_map_localizationAway
    {σ : Type} (A : Type) [CommRing A] {ι : Type} (r : ι → A) (hr : Ideal.span (Set.range r) = ⊤)
    (I : Ideal (MvPolynomial σ A)) (f : MvPolynomial σ A) :
    f ∈ I ↔ ∀ i : ι,
      MvPolynomial.map (algebraMap A (Localization.Away (r i))) f ∈
        Ideal.map (MvPolynomial.map (algebraMap A (Localization.Away (r i)))) I := by p2m_exact_reverting @_root_.P2MW.S_MvPolynomial_mem_ideal_iff_forall_map_mem_map_localizationAway.solution
