import Mathlib
import Definitions.Def_Dieudonne_DatumAndHonda
import Definitions.Def_Dieudonne_WittVectorHom
import Definitions.Def_Dieudonne_WittHomColimit
import Definitions.Def_Dieudonne_FontaineHodge
import P2M.Util
import P2M.Sol.S_Deformation_mem_wittHom_of_mem_fontaineKer_of_verschiebung_mem_wittHom

universe u v w

theorem Deformation.mem_wittHom_of_mem_fontaineKer_of_verschiebung_mem_wittHom
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    {k : Type v} [CommRing k] [Algebra 𝓞 k]
    (hk : Function.Surjective (algebraMap 𝓞 k))
    (hker : RingHom.ker (algebraMap 𝓞 k) = Ideal.span {(p : 𝓞)})
    (ℛ : Type w) [CommRing ℛ] [Bialgebra 𝓞 ℛ] [Module.Flat 𝓞 ℛ]
    {n : ℕ} {a : TruncatedWittVector p n (TensorProduct 𝓞 k ℛ)}
    (ha : a ∈ Deformation.TruncWitt.fontaineKer p n
      (Algebra.TensorProduct.includeRight : ℛ →ₐ[𝓞] TensorProduct 𝓞 k ℛ).toRingHom)
    (hVa : Deformation.TruncWitt.verschiebung a ∈
      Deformation.wittHom k p n (TensorProduct 𝓞 k ℛ)) :
    a ∈ Deformation.wittHom k p n (TensorProduct 𝓞 k ℛ) := by p2m_exact_reverting @_root_.P2MW.S_Deformation_mem_wittHom_of_mem_fontaineKer_of_verschiebung_mem_wittHom.solution
