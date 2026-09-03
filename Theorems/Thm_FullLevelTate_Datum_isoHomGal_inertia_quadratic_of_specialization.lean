import Definitions.Def_FullLevelTate_IsoHom
import Definitions.Def_DrinfeldCurve_CoordRing
import Definitions.Def_GaloisRep_TameCharacter
import P2M.Util
import P2M.Sol.S_FullLevelTate_Datum_isoHomGal_inertia_quadratic_of_specialization

set_option autoImplicit false

open scoped TensorProduct

theorem FullLevelTate.Datum.isoHomGal_inertia_quadratic_of_specialization
    (q : ℕ) [Fact q.Prime] (M' : ℕ) (O' : Type) [CommRing O'] [IsLocalRing O']
    (D : FullLevelTate.Datum q M' O')
    (K : Type) [Field K] [Algebra O' K]
    (θ : (GaloisField q 2)ˣ →* Kˣ) {W : Type} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (σ : Representation K (CuspidalType.GL2 q) W) (hσ : CuspidalType.IsCuspidalOfType θ σ)
    (P : ValuationSubring (AlgebraicClosure ℚ))
    (π : AlgebraicClosure ℚ) (hπ : π ^ (q ^ 2 - 1) = (q : AlgebraicClosure ℚ))
    (ι : GaloisField q 2 →+* IsLocalRing.ResidueField P)
    (T : Type) [AddCommGroup T] [Module K T] (ρT : ↥(DrinfeldCurve.hSubgroup q) →* Module.End K T)
    (hT : ∀ u : W →ₗ[K] T,
      (∀ (g : CuspidalType.GL2 q) (hg₁ : (g, (1 : (GaloisField q 2)ˣ)) ∈ DrinfeldCurve.hSubgroup q),
        u ∘ₗ σ g = ρT ⟨(g, 1), hg₁⟩ ∘ₗ u) →
      ∀ (α : (GaloisField q 2)ˣ) (g : CuspidalType.GL2 q) (hg : (g, α) ∈ DrinfeldCurve.hSubgroup q),
        let A : (W →ₗ[K] T) → (W →ₗ[K] T) := fun v => ρT ⟨(g, α), hg⟩ ∘ₗ v ∘ₗ σ g⁻¹
        A (A u) - (((θ α : Kˣ) : K) + ((θ (α ^ q) : Kˣ) : K)) • A u +
          (((θ α : Kˣ) : K) * ((θ (α ^ q) : Kˣ) : K)) • u = 0)
    (sp : K ⊗[O'] D.V →ₗ[K] T)
    (hsp : ∀ τ ∈ P.inertiaSubgroupIn ℚ, ∀ α : (GaloisField q 2)ˣ,
      ι (α : GaloisField q 2) = P.tameCharacter π τ →
        ∀ (g : CuspidalType.GL2 q) (hg : (g, α) ∈ DrinfeldCurve.hSubgroup q),
          sp ∘ₗ ((D.gl2 g * D.gal τ).baseChange K) = ρT ⟨(g, α), hg⟩ ∘ₗ sp)
    (U : Submodule K ↥(D.isoHom K (σ.comp (⊤ : Subgroup (CuspidalType.GL2 q)).subtype)))
    (hU : ∀ τ ∈ P.inertiaSubgroupIn ℚ, ∀ f ∈ U,
      D.isoHomGal K (σ.comp (⊤ : Subgroup (CuspidalType.GL2 q)).subtype) τ f ∈ U)
    (hinj : ∀ f ∈ U,
      sp ∘ₗ (f : W →ₗ[K] K ⊗[O'] D.V) = 0 → f = 0) :
    ∀ τ ∈ P.inertiaSubgroupIn ℚ, ∀ α : (GaloisField q 2)ˣ,
      ι (α : GaloisField q 2) = P.tameCharacter π τ →
        ∀ f ∈ U,
          ((D.isoHomGal K (σ.comp (⊤ : Subgroup (CuspidalType.GL2 q)).subtype) τ
                (D.isoHomGal K (σ.comp (⊤ : Subgroup (CuspidalType.GL2 q)).subtype) τ f) :
                ↥(D.isoHom K (σ.comp (⊤ : Subgroup (CuspidalType.GL2 q)).subtype))) :
              W →ₗ[K] K ⊗[O'] D.V) -
            (((θ α : Kˣ) : K) + ((θ (α ^ q) : Kˣ) : K)) •
              ((D.isoHomGal K (σ.comp (⊤ : Subgroup (CuspidalType.GL2 q)).subtype) τ f :
                  ↥(D.isoHom K (σ.comp (⊤ : Subgroup (CuspidalType.GL2 q)).subtype))) :
                W →ₗ[K] K ⊗[O'] D.V) +
            (((θ α : Kˣ) : K) * ((θ (α ^ q) : Kˣ) : K)) •
              ((f : ↥(D.isoHom K (σ.comp (⊤ : Subgroup (CuspidalType.GL2 q)).subtype))) :
                W →ₗ[K] K ⊗[O'] D.V) = 0 := by p2m_exact_reverting @_root_.P2MW.S_FullLevelTate_Datum_isoHomGal_inertia_quadratic_of_specialization.solution
