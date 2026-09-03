import Mathlib
import Definitions.Def_Dieudonne_DatumAndHonda
import Definitions.Def_Dieudonne_WittVectorHom
import Definitions.Def_Dieudonne_WittHomColimit
import Definitions.Def_Dieudonne_FontaineHodge
import P2M.Util
import P2M.Sol.S_Deformation_exists_algHom_baseChange_eq_of_faithfullyFlat_of_ker_eq_map_ker_counit

universe u v w₁ w₂ w₃ w'

theorem Deformation.exists_algHom_baseChange_eq_of_faithfullyFlat_of_ker_eq_map_ker_counit
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    {k : Type v} [CommRing k] [Algebra 𝓞 k]
    (hk : Function.Surjective (algebraMap 𝓞 k))
    (hker : RingHom.ker (algebraMap 𝓞 k) = Ideal.span {(p : 𝓞)})
    {ℛ : Type w₁} [CommRing ℛ] [HopfAlgebra 𝓞 ℛ]
    {ℛ₁ : Type w₂} [CommRing ℛ₁] [Bialgebra 𝓞 ℛ₁]
    {ℛ₃ : Type w₃} [CommRing ℛ₃] [Bialgebra 𝓞 ℛ₃]
    (π : ℛ →ₐc[𝓞] ℛ₁) (hπ : Function.Surjective π)
    (j : ℛ₃ →ₐc[𝓞] ℛ)
    (hexact : RingHom.ker (π : ℛ →ₐ[𝓞] ℛ₁) =
      Ideal.map (j : ℛ₃ →ₐ[𝓞] ℛ) (RingHom.ker (Bialgebra.counitAlgHom 𝓞 ℛ₃)))
    (hff : (j : ℛ₃ →ₐ[𝓞] ℛ).toRingHom.FaithfullyFlat)
    (hfin : (j : ℛ₃ →ₐ[𝓞] ℛ).toRingHom.Finite)
    (hL : ∀ z ∈ Deformation.fontaineHodge k p
        (Algebra.TensorProduct.includeRight : ℛ₁ →ₐ[𝓞] TensorProduct 𝓞 k ℛ₁).toRingHom,
      ∃ y ∈ Deformation.fontaineHodge k p
          (Algebra.TensorProduct.includeRight : ℛ →ₐ[𝓞] TensorProduct 𝓞 k ℛ).toRingHom,
        Deformation.DieudonneModule.map k p
          (Bialgebra.TensorProduct.map (BialgHom.id k k) π) y = z)
    (hG₁ : ∀ (Y' : Type (max w₁ w')) [CommRing Y'] [Algebra 𝓞 Y'] [Module.Finite 𝓞 Y']
        [Module.Flat 𝓞 Y'] (ψ : TensorProduct 𝓞 k ℛ₁ →ₐ[k] TensorProduct 𝓞 k Y'),
      (∀ (n : ℕ) (m : Deformation.wittHom k p n (TensorProduct 𝓞 k ℛ₁)),
        (m : TruncatedWittVector p n (TensorProduct 𝓞 k ℛ₁)) ∈ Deformation.TruncWitt.fontaineKer p n
            (Algebra.TensorProduct.includeRight : ℛ₁ →ₐ[𝓞] TensorProduct 𝓞 k ℛ₁).toRingHom →
          Deformation.TruncWitt.map ψ.toRingHom (m : TruncatedWittVector p n (TensorProduct 𝓞 k ℛ₁)) ∈
            Deformation.TruncWitt.fontaineKer p n
              (Algebra.TensorProduct.includeRight : Y' →ₐ[𝓞] TensorProduct 𝓞 k Y').toRingHom) →
      ∃ x : ℛ₁ →ₐ[𝓞] Y', Algebra.TensorProduct.map (AlgHom.id k k) x = ψ)
    (hG : ∀ (Y' : Type (max w₁ w')) [CommRing Y'] [Algebra 𝓞 Y'] [Module.Finite 𝓞 Y']
        [Module.Flat 𝓞 Y'] (y y' : ℛ →ₐ[𝓞] Y'),
      Algebra.TensorProduct.map (AlgHom.id k k) y = Algebra.TensorProduct.map (AlgHom.id k k) y' →
        y = y')
    (Y : Type w') [CommRing Y] [Algebra 𝓞 Y] [Module.Finite 𝓞 Y] [Module.Flat 𝓞 Y]
    (hG₃ : ∀ ψ : TensorProduct 𝓞 k ℛ₃ →ₐ[k] TensorProduct 𝓞 k Y,
      (∀ (n : ℕ) (m : Deformation.wittHom k p n (TensorProduct 𝓞 k ℛ₃)),
        (m : TruncatedWittVector p n (TensorProduct 𝓞 k ℛ₃)) ∈ Deformation.TruncWitt.fontaineKer p n
            (Algebra.TensorProduct.includeRight : ℛ₃ →ₐ[𝓞] TensorProduct 𝓞 k ℛ₃).toRingHom →
          Deformation.TruncWitt.map ψ.toRingHom (m : TruncatedWittVector p n (TensorProduct 𝓞 k ℛ₃)) ∈
            Deformation.TruncWitt.fontaineKer p n
              (Algebra.TensorProduct.includeRight : Y →ₐ[𝓞] TensorProduct 𝓞 k Y).toRingHom) →
      ∃ x : ℛ₃ →ₐ[𝓞] Y, Algebra.TensorProduct.map (AlgHom.id k k) x = ψ)
    (χ : TensorProduct 𝓞 k ℛ →ₐ[k] TensorProduct 𝓞 k Y)
    (hχ : ∀ (n : ℕ) (m : Deformation.wittHom k p n (TensorProduct 𝓞 k ℛ)),
      (m : TruncatedWittVector p n (TensorProduct 𝓞 k ℛ)) ∈ Deformation.TruncWitt.fontaineKer p n
          (Algebra.TensorProduct.includeRight : ℛ →ₐ[𝓞] TensorProduct 𝓞 k ℛ).toRingHom →
        Deformation.TruncWitt.map χ.toRingHom (m : TruncatedWittVector p n (TensorProduct 𝓞 k ℛ)) ∈
          Deformation.TruncWitt.fontaineKer p n
            (Algebra.TensorProduct.includeRight : Y →ₐ[𝓞] TensorProduct 𝓞 k Y).toRingHom) :
    ∃ x : ℛ →ₐ[𝓞] Y, Algebra.TensorProduct.map (AlgHom.id k k) x = χ := by p2m_exact_reverting @_root_.P2MW.S_Deformation_exists_algHom_baseChange_eq_of_faithfullyFlat_of_ker_eq_map_ker_counit.solution
