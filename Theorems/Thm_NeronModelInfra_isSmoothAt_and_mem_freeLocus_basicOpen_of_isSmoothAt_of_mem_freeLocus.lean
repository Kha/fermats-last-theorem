import Mathlib
import Definitions.Def_NeronModelInfra_WeakNeronModel
import Definitions.Def_NeronModelInfra_SmoothnessDefect
import P2M.Util
import P2M.Sol.S_NeronModelInfra_isSmoothAt_and_mem_freeLocus_basicOpen_of_isSmoothAt_of_mem_freeLocus

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra TensorProduct

universe u

theorem NeronModelInfra.isSmoothAt_and_mem_freeLocus_basicOpen_of_isSmoothAt_of_mem_freeLocus
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType f]
    (C : Set X) (hC : ∀ y ∈ C, f y = IsLocalRing.closedPoint R)
    (U : X.Opens) (hU : IsAffineOpen U) (h : Γ(X, U)) (y : X) (hyU : y ∈ U) (hyh : y ∈ X.basicOpen h) :
    letI : Algebra R Γ(X, U) :=
      ((X.presheaf.map (homOfLE le_top).op).hom.comp
        (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)).toAlgebra
    letI : Algebra R Γ(X, X.basicOpen h) :=
      ((X.presheaf.map (homOfLE le_top).op).hom.comp
        (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)).toAlgebra
    let J : Ideal Γ(X, U) :=
      PrimeSpectrum.vanishingIdeal ((fun z : U => hU.primeIdealOf z) '' {z : U | (z : X) ∈ C})
    let J' : Ideal Γ(X, X.basicOpen h) :=
      PrimeSpectrum.vanishingIdeal ((fun z : X.basicOpen h => (hU.basicOpen h).primeIdealOf z) ''
        {z : X.basicOpen h | (z : X) ∈ C})
    (∀ (𝔮 : Ideal (Γ(X, U) ⧸ J)) [𝔮.IsPrime],
      𝔮.comap (Ideal.Quotient.mk J) = (hU.primeIdealOf ⟨y, hyU⟩).asIdeal →
      (∀ [Algebra (IsLocalRing.ResidueField R) (Γ(X, U) ⧸ J)]
        [IsScalarTower R (IsLocalRing.ResidueField R) (Γ(X, U) ⧸ J)],
        Algebra.IsSmoothAt (IsLocalRing.ResidueField R) 𝔮) ∧
      (⟨𝔮, ‹_›⟩ : PrimeSpectrum (Γ(X, U) ⧸ J)) ∈
        Module.freeLocus (Γ(X, U) ⧸ J) ((Γ(X, U) ⧸ J) ⊗[Γ(X, U)] Ω[Γ(X, U)⁄R])) →
    ∀ (𝔮' : Ideal (Γ(X, X.basicOpen h) ⧸ J')) [𝔮'.IsPrime],
      𝔮'.comap (Ideal.Quotient.mk J') = ((hU.basicOpen h).primeIdealOf ⟨y, hyh⟩).asIdeal →
      (∀ [Algebra (IsLocalRing.ResidueField R) (Γ(X, X.basicOpen h) ⧸ J')]
        [IsScalarTower R (IsLocalRing.ResidueField R) (Γ(X, X.basicOpen h) ⧸ J')],
        Algebra.IsSmoothAt (IsLocalRing.ResidueField R) 𝔮') ∧
      (⟨𝔮', ‹_›⟩ : PrimeSpectrum (Γ(X, X.basicOpen h) ⧸ J')) ∈
        Module.freeLocus (Γ(X, X.basicOpen h) ⧸ J')
          ((Γ(X, X.basicOpen h) ⧸ J') ⊗[Γ(X, X.basicOpen h)] Ω[Γ(X, X.basicOpen h)⁄R]) := by p2m_exact_reverting @_root_.P2MW.S_NeronModelInfra_isSmoothAt_and_mem_freeLocus_basicOpen_of_isSmoothAt_of_mem_freeLocus.solution
