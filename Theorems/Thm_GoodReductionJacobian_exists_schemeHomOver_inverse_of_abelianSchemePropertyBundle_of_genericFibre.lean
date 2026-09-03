import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_exists_schemeHomOver_inverse_of_abelianSchemePropertyBundle_of_genericFibre
attribute [-instance] instTopologicallyFGOfFiniteType
attribute [-simp] RegularLocalRingQuotientAscent.dualNumberFst_apply

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.exists_schemeHomOver_inverse_of_abelianSchemePropertyBundle_of_genericFibre
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {A₁ A₂ : Scheme.{u}} {f₁ : A₁ ⟶ Spec (CommRingCat.of R)} {f₂ : A₂ ⟶ Spec (CommRingCat.of R)}
    (h₁ : AbelianSchemePropertyBundle R f₁) (h₂ : AbelianSchemePropertyBundle R f₂)
    (φK : SchemeHomOver (pullback.snd f₁ (specGenericFibreInclusion R K))
      (pullback.snd f₂ (specGenericFibreInclusion R K)))
    (ψK : SchemeHomOver (pullback.snd f₂ (specGenericFibreInclusion R K))
      (pullback.snd f₁ (specGenericFibreInclusion R K)))
    (hφψ : φK.1 ≫ ψK.1 = 𝟙 _) (hψφ : ψK.1 ≫ φK.1 = 𝟙 _) :
    ∃ (φ : SchemeHomOver f₁ f₂) (ψ : SchemeHomOver f₂ f₁),
      genericFibreRestrict R K f₂ f₁ φ = φK ∧ genericFibreRestrict R K f₁ f₂ ψ = ψK ∧
      φ.1 ≫ ψ.1 = 𝟙 A₁ ∧ ψ.1 ≫ φ.1 = 𝟙 A₂ ∧
      (∀ φ' : SchemeHomOver f₁ f₂, genericFibreRestrict R K f₂ f₁ φ' = φK → φ' = φ) := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_exists_schemeHomOver_inverse_of_abelianSchemePropertyBundle_of_genericFibre.solution
