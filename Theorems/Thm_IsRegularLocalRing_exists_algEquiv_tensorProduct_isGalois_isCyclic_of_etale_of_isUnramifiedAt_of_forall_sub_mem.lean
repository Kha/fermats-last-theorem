import Mathlib
import P2M.Util
import P2M.Sol.S_IsRegularLocalRing_exists_algEquiv_tensorProduct_isGalois_isCyclic_of_etale_of_isUnramifiedAt_of_forall_sub_mem

set_option autoImplicit false

open IsLocalRing Polynomial
open scoped TensorProduct

universe u v w x

theorem IsRegularLocalRing.exists_algEquiv_tensorProduct_isGalois_isCyclic_of_etale_of_isUnramifiedAt_of_forall_sub_mem
    {R : Type u} [CommRing R] [IsRegularLocalRing R] [IsDomain R] [IsAdicComplete (maximalIdeal R) R]
    (ϖ s : R) (hmax : maximalIdeal R = Ideal.span {ϖ, s}) (hdim : ringKrullDim R = 2)
    (e : ℕ) (he : 0 < e) (heR : IsUnit (e : R))
    (B : Type v) [CommRing B] [IsDomain B] [IsIntegrallyClosed B] [IsLocalRing B] [IsNoetherianRing B]
    [Algebra R B] [Module.Finite R B] [FaithfulSMul R B]
    (K₀ : Type w) [Field K₀] [Algebra R K₀] [IsFractionRing R K₀]
    (F : Type x) [Field F] [Algebra K₀ F] [Algebra R F] [IsScalarTower R K₀ F]
    [Algebra B F] [IsScalarTower R B F] [IsFractionRing B F]
    [FiniteDimensional K₀ F] [IsGalois K₀ F] (hcyc : IsCyclic (F ≃ₐ[K₀] F)) (hdeg : Module.finrank K₀ F = e)
    (hunr : ∀ (𝔭 : Ideal B) [𝔭.IsPrime], (𝔭.comap (algebraMap R B)).height = 1 →
      s ∉ 𝔭.comap (algebraMap R B) → Algebra.IsUnramifiedAt R 𝔭)
    (hres : ∀ b : B, ∃ r : R, b - algebraMap R B r ∈ maximalIdeal B)
    (R' : Type u) [CommRing R'] [IsRegularLocalRing R'] [IsDomain R'] [Algebra R R']
    [Module.Finite R R'] [Module.Free R R'] [FaithfulSMul R R'] [Algebra.Etale R R']
    [IsAdicComplete (maximalIdeal R') R'] :
    ∃ (B' : Type (max u v)) (_ : CommRing B') (_ : IsDomain B') (_ : IsIntegrallyClosed B') (_ : IsLocalRing B')
      (_ : IsNoetherianRing B') (_ : Algebra R' B') (_ : Module.Finite R' B') (_ : FaithfulSMul R' B')
      (K₀' : Type u) (_ : Field K₀') (_ : Algebra R' K₀') (_ : IsFractionRing R' K₀')
      (F' : Type (max u v)) (_ : Field F') (_ : Algebra K₀' F') (_ : Algebra R' F') (_ : IsScalarTower R' K₀' F')
      (_ : Algebra B' F') (_ : IsScalarTower R' B' F') (_ : IsFractionRing B' F')
      (_ : FiniteDimensional K₀' F') (_ : IsGalois K₀' F'),
      IsCyclic (F' ≃ₐ[K₀'] F') ∧ Module.finrank K₀' F' = e ∧
      (∀ (𝔭 : Ideal B') [𝔭.IsPrime], (𝔭.comap (algebraMap R' B')).height = 1 →
        algebraMap R R' s ∉ 𝔭.comap (algebraMap R' B') → Algebra.IsUnramifiedAt R' 𝔭) ∧
      (∀ b : B', ∃ r : R', b - algebraMap R' B' r ∈ maximalIdeal B') ∧
      Nonempty (R' ⊗[R] B ≃ₐ[R'] B') := by p2m_exact_reverting @_root_.P2MW.S_IsRegularLocalRing_exists_algEquiv_tensorProduct_isGalois_isCyclic_of_etale_of_isUnramifiedAt_of_forall_sub_mem.solution
