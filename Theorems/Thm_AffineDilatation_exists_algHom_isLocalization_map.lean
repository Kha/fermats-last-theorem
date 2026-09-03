import Mathlib
import Definitions.Def_RingTheory_AffineDilatation
import P2M.Util
import P2M.Sol.S_AffineDilatation_exists_algHom_isLocalization_map

set_option autoImplicit false

universe u v

theorem AffineDilatation.exists_algHom_isLocalization_map
    {A : Type u} [CommRing A] (I : Ideal A) (a : A) (ha : a ∈ I)
    (M : Submonoid A) (A' : Type v) [CommRing A'] [Algebra A A'] [IsLocalization M A'] :
    ∃ φ : AffineDilatation.Ring I a →ₐ[A]
        AffineDilatation.Ring (I.map (algebraMap A A')) (algebraMap A A' a),
      @IsLocalization _ _ (Algebra.algebraMapSubmonoid (AffineDilatation.Ring I a) M)
        (AffineDilatation.Ring (I.map (algebraMap A A')) (algebraMap A A' a)) _
        φ.toRingHom.toAlgebra := by p2m_exact_reverting @_root_.P2MW.S_AffineDilatation_exists_algHom_isLocalization_map.solution
