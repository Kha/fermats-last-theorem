import Mathlib
import Definitions.Def_ModularCurve_LaurentCoeff
import P2M.Util
import P2M.Sol.S_ValuationSubring_exists_fractionRing_tensorProduct_quotient_algEquiv_apply_tmul_eq_coeffMap_of_residueField_ringEquiv

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

open scoped TensorProduct

theorem ValuationSubring.exists_fractionRing_tensorProduct_quotient_algEquiv_apply_tmul_eq_coeffMap_of_residueField_ringEquiv
    (A : Type) [CommRing A] [IsLocalRing A]
    (k : Type) [Field k] [Algebra A k] (hk : ∀ a ∈ IsLocalRing.maximalIdeal A, algebraMap A k a = 0)
    [Algebra (IsLocalRing.ResidueField A) k]
    (hκk : ∀ a : A, algebraMap (IsLocalRing.ResidueField A) k (IsLocalRing.residue A a) = algebraMap A k a)
    {K : Type} [Field K] [Algebra A K]
    (V : ValuationSubring K) (hVA : ∀ a : A, algebraMap A K a ∈ V)
    [Algebra A ↥V] (halgV : ∀ a : A, ((algebraMap A ↥V a : ↥V) : K) = algebraMap A K a)
    (ϖ : A) (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ})
    (hunif : ∀ f : K, f ∈ V.nonunits → ∃ g : K, g ∈ V ∧ f = algebraMap A K ϖ * g)
    (E : IntermediateField (IsLocalRing.ResidueField A) (LaurentSeries (IsLocalRing.ResidueField A)))
    (θ : IsLocalRing.ResidueField ↥V ≃+* ↥E)
    (hθ : ∀ a : A, θ (IsLocalRing.residue ↥V ⟨algebraMap A K a, hVA a⟩) =
      algebraMap (IsLocalRing.ResidueField A) ↥E (IsLocalRing.residue A a))
    (hLD : ∀ (n : ℕ) (f : Fin n → LaurentSeries (IsLocalRing.ResidueField A)),
      LinearIndependent (IsLocalRing.ResidueField A) f →
      LinearIndependent k (⇑(ModularCurve.coeffMap (algebraMap (IsLocalRing.ResidueField A) k)) ∘ f))
    (E' : IntermediateField k (LaurentSeries k))
    (hE' : IntermediateField.adjoin k
      (⇑(ModularCurve.coeffMap (algebraMap (IsLocalRing.ResidueField A) k)) '' ((E : Set (LaurentSeries (IsLocalRing.ResidueField A))))) = E')
    (𝔮 : Ideal (k ⊗[A] ↥V)) (h𝔮 : 𝔮 ∈ minimalPrimes (k ⊗[A] ↥V)) :
    ∃ Φ : FractionRing ((k ⊗[A] ↥V) ⧸ 𝔮) ≃ₐ[k] ↥E',
      ∀ v : ↥V,
        (((Φ (Localization.mk (Ideal.Quotient.mk 𝔮 ((1 : k) ⊗ₜ[A] v)) 1)) : ↥E') : LaurentSeries k)
          = ModularCurve.coeffMap (algebraMap (IsLocalRing.ResidueField A) k)
              ((θ (IsLocalRing.residue ↥V v) : ↥E) : LaurentSeries (IsLocalRing.ResidueField A)) := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_exists_fractionRing_tensorProduct_quotient_algEquiv_apply_tmul_eq_coeffMap_of_residueField_ringEquiv.solution
