import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_isClosed_of_forall_exists_isOpenImmersion_forall_mem_iff_le

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.isClosed_of_forall_exists_isOpenImmersion_forall_mem_iff_le
    {E : Scheme.{u}} (T : Set E)
    (h : ∀ e : E, ∃ (S : Type u) (_ : CommRing S) (ι : Spec (CommRingCat.of S) ⟶ E) (_ : IsOpenImmersion ι)
        (I : Ideal S), e ∈ Set.range ι.base ∧ ∀ 𝔮 : PrimeSpectrum S, ι.base 𝔮 ∈ T ↔ I ≤ 𝔮.asIdeal) :
    IsClosed T := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_isClosed_of_forall_exists_isOpenImmersion_forall_mem_iff_le.solution
