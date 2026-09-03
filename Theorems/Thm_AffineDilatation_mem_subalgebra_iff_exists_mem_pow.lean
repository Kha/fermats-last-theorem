import Mathlib
import Definitions.Def_RingTheory_AffineDilatation
import P2M.Util
import P2M.Sol.S_AffineDilatation_mem_subalgebra_iff_exists_mem_pow

set_option autoImplicit false

universe u

theorem AffineDilatation.mem_subalgebra_iff_exists_mem_pow
    {A : Type u} [CommRing A] (I : Ideal A) (a : A) (ha : a ∈ I) (x : Localization.Away a) :
    x ∈ AffineDilatation.subalgebra I a ↔
      ∃ (n : ℕ) (g : A), g ∈ I ^ n ∧
        IsLocalization.mk' (Localization.Away a) g (⟨a ^ n, n, rfl⟩ : Submonoid.powers a) = x := by p2m_exact_reverting @_root_.P2MW.S_AffineDilatation_mem_subalgebra_iff_exists_mem_pow.solution
