import Mathlib
import Definitions.Def_Dieudonne_DatumAndHonda
import Definitions.Def_Dieudonne_WittVectorHom
import Definitions.Def_Dieudonne_WittHomColimit
import Definitions.Def_Dieudonne_FontaineHodge
import P2M.Util
import P2M.Sol.S_Deformation_DieudonneModule_exists_hondaSystem_L_eq_fontaineHodge

universe u v w

theorem Deformation.DieudonneModule.exists_hondaSystem_L_eq_fontaineHodge
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    {k : Type v} [Field k] [CharP k p] [PerfectRing k p] [Algebra 𝓞 k]
    (hk : Function.Surjective (algebraMap 𝓞 k))
    (hker : RingHom.ker (algebraMap 𝓞 k) = Ideal.span {(p : 𝓞)})
    (ℛ : Type w) [CommRing ℛ] [HopfAlgebra 𝓞 ℛ] [Coalgebra.IsCocomm 𝓞 ℛ]
    [Module.Free 𝓞 ℛ] [Module.Finite 𝓞 ℛ] (hrank : ∃ a : ℕ, Module.finrank 𝓞 ℛ = p ^ a) :
    ∃ H : Deformation.HondaSystem (p : ℤ) (Deformation.DieudonneModule k p (TensorProduct 𝓞 k ℛ)),
      H.toDieudonneDatum = Deformation.DieudonneModule.dieudonneDatum k p (TensorProduct 𝓞 k ℛ) ∧
      H.L = Deformation.fontaineHodge k p
        (Algebra.TensorProduct.includeRight : ℛ →ₐ[𝓞] TensorProduct 𝓞 k ℛ).toRingHom := by p2m_exact_reverting @_root_.P2MW.S_Deformation_DieudonneModule_exists_hondaSystem_L_eq_fontaineHodge.solution
