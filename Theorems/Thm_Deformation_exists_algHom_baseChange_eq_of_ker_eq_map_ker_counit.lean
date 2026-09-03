import Mathlib
import Definitions.Def_Dieudonne_DatumAndHonda
import Definitions.Def_Dieudonne_WittVectorHom
import Definitions.Def_Dieudonne_WittHomColimit
import Definitions.Def_Dieudonne_FontaineHodge
import P2M.Util
import P2M.Sol.S_Deformation_exists_algHom_baseChange_eq_of_ker_eq_map_ker_counit

universe u v w₁ w₂ w₃ w'

theorem Deformation.exists_algHom_baseChange_eq_of_ker_eq_map_ker_counit
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime]
    {k : Type v} [CommRing k] [Algebra 𝓞 k]
    {𝒮 : Type w₁} [CommRing 𝒮] [Bialgebra 𝓞 𝒮]
    {𝒮' : Type w₂} [CommRing 𝒮'] [Bialgebra 𝓞 𝒮']
    {ℛ : Type w₃} [CommRing ℛ] [Bialgebra 𝓞 ℛ]
    (φ : 𝒮' →ₐc[𝓞] 𝒮) (q : 𝒮 →ₐc[𝓞] ℛ) (hq : Function.Surjective q)
    (hexact : RingHom.ker (q : 𝒮 →ₐ[𝓞] ℛ) =
      Ideal.map (φ : 𝒮' →ₐ[𝓞] 𝒮) (RingHom.ker (Bialgebra.counitAlgHom 𝓞 𝒮')))
    (Y : Type w') [CommRing Y] [Algebra 𝓞 Y]
    (hH : ∀ ψ : TensorProduct 𝓞 k 𝒮 →ₐ[k] TensorProduct 𝓞 k Y,
      (∀ (n : ℕ) (m : Deformation.wittHom k p n (TensorProduct 𝓞 k 𝒮)),
        (m : TruncatedWittVector p n (TensorProduct 𝓞 k 𝒮)) ∈ Deformation.TruncWitt.fontaineKer p n
            (Algebra.TensorProduct.includeRight : 𝒮 →ₐ[𝓞] TensorProduct 𝓞 k 𝒮).toRingHom →
          Deformation.TruncWitt.map ψ.toRingHom (m : TruncatedWittVector p n (TensorProduct 𝓞 k 𝒮)) ∈
            Deformation.TruncWitt.fontaineKer p n
              (Algebra.TensorProduct.includeRight : Y →ₐ[𝓞] TensorProduct 𝓞 k Y).toRingHom) →
      ∃ x : 𝒮 →ₐ[𝓞] Y, Algebra.TensorProduct.map (AlgHom.id k k) x = ψ)
    (hH' : ∀ y y' : 𝒮' →ₐ[𝓞] Y,
      Algebra.TensorProduct.map (AlgHom.id k k) y = Algebra.TensorProduct.map (AlgHom.id k k) y' →
        y = y')
    (χ : TensorProduct 𝓞 k ℛ →ₐ[k] TensorProduct 𝓞 k Y)
    (hχ : ∀ (n : ℕ) (m : Deformation.wittHom k p n (TensorProduct 𝓞 k ℛ)),
      (m : TruncatedWittVector p n (TensorProduct 𝓞 k ℛ)) ∈ Deformation.TruncWitt.fontaineKer p n
          (Algebra.TensorProduct.includeRight : ℛ →ₐ[𝓞] TensorProduct 𝓞 k ℛ).toRingHom →
        Deformation.TruncWitt.map χ.toRingHom (m : TruncatedWittVector p n (TensorProduct 𝓞 k ℛ)) ∈
          Deformation.TruncWitt.fontaineKer p n
            (Algebra.TensorProduct.includeRight : Y →ₐ[𝓞] TensorProduct 𝓞 k Y).toRingHom) :
    ∃ x : ℛ →ₐ[𝓞] Y, Algebra.TensorProduct.map (AlgHom.id k k) x = χ := by p2m_exact_reverting @_root_.P2MW.S_Deformation_exists_algHom_baseChange_eq_of_ker_eq_map_ker_counit.solution
