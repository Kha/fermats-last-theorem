import Mathlib
import Definitions.Def_ArtinL_Abelian
import P2M.Util
import P2M.Sol.S_ArtinL_Abelian_exists_inertia_pow_eq_map_conj_ramificationGroup_of_under_eq

set_option autoImplicit false

open NumberField IsDedekindDomain

universe u v

theorem ArtinL.Abelian.exists_inertia_pow_eq_map_conj_ramificationGroup_of_under_eq
    (K : Type u) (M : Type v) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
    [IsGalois K M] (v : HeightOneSpectrum (𝓞 K))
    (Q : Ideal (𝓞 M)) [Q.IsMaximal] (hQ : Q.under (𝓞 K) = v.asIdeal) :
    ∃ τ : M ≃ₐ[K] M,
      (∀ x : 𝓞 M, x ∈ LanglandsTunnell.P2.Artin.primeAbove K M v ↔ τ • x ∈ Q) ∧
      ∀ i : ℕ,
        (Q ^ (i + 1)).inertia (M ≃ₐ[K] M) = (ArtinL.Abelian.ramificationGroup K M v i).map (MulAut.conj τ).toMonoidHom ∧
        Nat.card ((Q ^ (i + 1)).inertia (M ≃ₐ[K] M)) = Nat.card (ArtinL.Abelian.ramificationGroup K M v i) ∧
        ∀ {A : Type*} [CommGroup A] (ψ : (M ≃ₐ[K] M) →* A),
          (∀ σ ∈ (Q ^ (i + 1)).inertia (M ≃ₐ[K] M), ψ σ = 1) ↔
            ∀ σ ∈ ArtinL.Abelian.ramificationGroup K M v i, ψ σ = 1 := by p2m_exact_reverting @_root_.P2MW.S_ArtinL_Abelian_exists_inertia_pow_eq_map_conj_ramificationGroup_of_under_eq.solution
