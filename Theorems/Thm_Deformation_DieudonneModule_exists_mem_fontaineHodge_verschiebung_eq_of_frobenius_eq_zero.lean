import Mathlib
import Definitions.Def_Dieudonne_DatumAndHonda
import Definitions.Def_Dieudonne_WittVectorHom
import Definitions.Def_Dieudonne_WittHomColimit
import Definitions.Def_Dieudonne_FontaineHodge
import P2M.Util
import P2M.Sol.S_Deformation_DieudonneModule_exists_mem_fontaineHodge_verschiebung_eq_of_frobenius_eq_zero

universe u v w

theorem Deformation.DieudonneModule.exists_mem_fontaineHodge_verschiebung_eq_of_frobenius_eq_zero
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    {k : Type v} [CommRing k] [CharP k p] [Algebra 𝓞 k]
    (hk : Function.Surjective (algebraMap 𝓞 k))
    (hker : RingHom.ker (algebraMap 𝓞 k) = Ideal.span {(p : 𝓞)})
    (ℛ : Type w) [CommRing ℛ] [Bialgebra 𝓞 ℛ] [Module.Flat 𝓞 ℛ]
    {z : Deformation.DieudonneModule k p (TensorProduct 𝓞 k ℛ)}
    (hz : Deformation.DieudonneModule.frobenius k p (TensorProduct 𝓞 k ℛ) z = 0) :
    ∃ y ∈ Deformation.fontaineHodge k p
        (Algebra.TensorProduct.includeRight : ℛ →ₐ[𝓞] TensorProduct 𝓞 k ℛ).toRingHom,
      Deformation.DieudonneModule.verschiebung k p (TensorProduct 𝓞 k ℛ) y = z := by p2m_exact_reverting @_root_.P2MW.S_Deformation_DieudonneModule_exists_mem_fontaineHodge_verschiebung_eq_of_frobenius_eq_zero.solution
