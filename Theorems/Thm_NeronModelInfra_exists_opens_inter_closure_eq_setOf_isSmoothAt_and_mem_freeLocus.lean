import Mathlib
import Definitions.Def_NeronModelInfra_WeakNeronModel
import Definitions.Def_NeronModelInfra_SmoothnessDefect
import P2M.Util
import P2M.Sol.S_NeronModelInfra_exists_opens_inter_closure_eq_setOf_isSmoothAt_and_mem_freeLocus

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra~exists_algHom_comap_maximalIdeal_eq_primeIdealOf_of_apply_closedPoint_mem TensorProduct"

universe u

theorem NeronModelInfra.exists_opens_inter_closure_eq_setOf_isSmoothAt_and_mem_freeLocus
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType f] (S : Set X)
    (hS : ∀ s ∈ S, ∃ (R' : Type u) (_ : CommRing R') (_ : IsDomain R') (_ : IsDiscreteValuationRing R') (_ : Algebra R R')
      (_ : IsLocalHom (algebraMap R R')) (_ : IsIndexOneExtension R R')
      (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R R'))) f), x.1 (IsLocalRing.closedPoint R') = s)
    (hSk : ∀ s ∈ S, f s = IsLocalRing.closedPoint R)
    (U : X.Opens) (hU : IsAffineOpen U) :
    letI : Algebra R Γ(X, U) :=
      ((X.presheaf.map (homOfLE le_top).op).hom.comp
        (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)).toAlgebra
    let J : Ideal Γ(X, U) :=
      PrimeSpectrum.vanishingIdeal ((fun z : U => hU.primeIdealOf z) '' {z : U | (z : X) ∈ closure S})
    ∃ W : X.Opens, (W : Set X) ⊆ U ∧
      ((closure S ∩ (U : Set X)).Nonempty → (closure S ∩ (W : Set X)).Nonempty) ∧
      ∀ (y : X) (hyU : y ∈ U), y ∈ closure S →
        (y ∈ W ↔
          ∀ (𝔮 : Ideal (Γ(X, U) ⧸ J)) [𝔮.IsPrime],
            𝔮.comap (Ideal.Quotient.mk J) = (hU.primeIdealOf ⟨y, hyU⟩).asIdeal →
            (∀ [Algebra (IsLocalRing.ResidueField R) (Γ(X, U) ⧸ J)]
              [IsScalarTower R (IsLocalRing.ResidueField R) (Γ(X, U) ⧸ J)],
              Algebra.IsSmoothAt (IsLocalRing.ResidueField R) 𝔮) ∧
            (⟨𝔮, ‹_›⟩ : PrimeSpectrum (Γ(X, U) ⧸ J)) ∈
              Module.freeLocus (Γ(X, U) ⧸ J) ((Γ(X, U) ⧸ J) ⊗[Γ(X, U)] Ω[Γ(X, U)⁄R])) := by p2m_exact_reverting @_root_.P2MW.S_NeronModelInfra_exists_opens_inter_closure_eq_setOf_isSmoothAt_and_mem_freeLocus.solution
