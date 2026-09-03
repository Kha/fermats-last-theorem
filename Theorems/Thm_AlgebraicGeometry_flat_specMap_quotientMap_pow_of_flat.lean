import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_flat_specMap_quotientMap_pow_of_flat

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry
theorem AlgebraicGeometry.flat_specMap_quotientMap_pow_of_flat
    (𝒪 : Type) [CommRing 𝒪] (π : 𝒪) (S : Type) [CommRing S] [Algebra 𝒪 S] [Module.Flat 𝒪 S] (n : ℕ) :
    Flat (Spec.map (CommRingCat.ofHom (Ideal.quotientMap (Ideal.span {(algebraMap 𝒪 S π) ^ (n + 1)}) (algebraMap 𝒪 S)
      (by rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_pow]; exact Ideal.subset_span rfl)))) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_flat_specMap_quotientMap_pow_of_flat.solution
