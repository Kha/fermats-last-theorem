import Mathlib
import P2M.Util
import P2M.Sol.S_IsLocalization_exists_algEquiv_tensorProduct_and_injective_of_bijective_baseChange

set_option autoImplicit false

open scoped TensorProduct

theorem IsLocalization.exists_algEquiv_tensorProduct_and_injective_of_bijective_baseChange
    {R S Rhat T K₁ K E : Type*}
    [CommRing R] [IsDomain R] [CommRing S] [IsDomain S] [CommRing Rhat] [IsDomain Rhat]
    [CommRing T] [Field K₁] [Field K] [Field E]

    [Algebra R S] [Module.Finite R S] [NoZeroSMulDivisors R S]
    [Algebra R K₁] [IsFractionRing R K₁] [Algebra S K] [IsFractionRing S K]
    [Algebra R K] [Algebra K₁ K] [IsScalarTower R S K] [IsScalarTower R K₁ K]

    [Algebra R Rhat] [FaithfulSMul R Rhat] [Module.Flat R Rhat]
    [Algebra Rhat E] [IsFractionRing Rhat E]
    [Algebra R E] [Algebra K₁ E] [IsScalarTower R Rhat E] [IsScalarTower R K₁ E]

    [Algebra Rhat T] [Algebra S T] [Algebra R T] [IsScalarTower R Rhat T] [IsScalarTower R S T]
    (hT : Function.Bijective
      (Algebra.TensorProduct.lift (Algebra.ofId Rhat T) (IsScalarTower.toAlgHom R S T)
        (fun _ _ => Commute.all _ _) : Rhat ⊗[R] S →ₐ[Rhat] T))

    (F₀ : Type*) [CommRing F₀] [Algebra T F₀] [Algebra Rhat F₀] [IsScalarTower Rhat T F₀]
    [IsLocalization (Algebra.algebraMapSubmonoid T (nonZeroDivisors Rhat)) F₀]
    [Algebra E F₀] [IsScalarTower Rhat E F₀] :
    (∃ e : (E ⊗[K₁] K) ≃ₐ[E] F₀,
      ∀ s : S, e ((1 : E) ⊗ₜ[K₁] algebraMap S K s) = algebraMap T F₀ (algebraMap S T s)) ∧
    Function.Injective (algebraMap T F₀) := by p2m_exact_reverting @_root_.P2MW.S_IsLocalization_exists_algEquiv_tensorProduct_and_injective_of_bijective_baseChange.solution
