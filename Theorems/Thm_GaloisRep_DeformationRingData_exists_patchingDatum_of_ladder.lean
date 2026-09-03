import Definitions.Def_GaloisRep_DeformationRingData
import Definitions.Def_Algebra_PatchingDatum
import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.RingTheory.Length
import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import P2M.Util
import P2M.Sol.S_GaloisRep_DeformationRingData_exists_patchingDatum_of_ladder

theorem GaloisRep.DeformationRingData.exists_patchingDatum_of_ladder
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪] [Finite (IsLocalRing.ResidueField 𝒪)]
    (p : ℕ) (hp𝒪 : (p : 𝒪) ∈ IsLocalRing.maximalIdeal 𝒪)
    (ρbar : ResidualGaloisRep (IsLocalRing.ResidueField 𝒪))

    (n : ℕ)
    (𝒟 : ℕ → ∀ ⦃A : Type⦄ [CommRing A] [IsLocalRing A] [Algebra 𝒪 A], GaloisRepAdic A → Prop)
    (hmono : ∀ k, k < n → ∀ ⦃A : Type⦄ [CommRing A] [IsLocalRing A] [Algebra 𝒪 A]
      (ρ : GaloisRepAdic A), 𝒟 (k + 1) ρ → 𝒟 k ρ)

    (T : ℕ → Type) [∀ k, CommRing (T k)] [∀ k, IsLocalRing (T k)] [∀ k, IsNoetherianRing (T k)]
    [∀ k, IsAdicComplete (IsLocalRing.maximalIdeal (T k)) (T k)] [∀ k, Algebra 𝒪 (T k)]
    [∀ k, IsLocalHom (algebraMap 𝒪 (T k))] [∀ k, Module.Finite 𝒪 (T k)] [∀ k, Module.Free 𝒪 (T k)]
    (ρT : ∀ k, GaloisRepAdic (T k))
    (πT : ∀ k, T k →ₐ[𝒪] 𝒪)
    (hη : ∀ k, k ≤ n → (RingHom.ker (πT k)).annihilator.map (πT k) ≠ ⊥)
    (M : ℕ → Type) [∀ k, AddCommGroup (M k)] [∀ k, Module (T k) (M k)] [∀ k, Module 𝒪 (M k)]
    [∀ k, IsScalarTower 𝒪 (T k) (M k)] [∀ k, Module.Finite 𝒪 (M k)] [∀ k, Module.Free 𝒪 (M k)]
    (B : ∀ k, M k →ₗ[𝒪] M k →ₗ[𝒪] 𝒪)
    (hB : ∀ k, k ≤ n → ∀ (t : T k) (m m' : M k), B k (t • m) m' = B k m (t • m'))
    (hBb : ∀ k, k ≤ n → Function.Bijective (B k))
    (hM : ∀ k, k ≤ n → Submodule.torsionBySet (T k) (M k) ↑(RingHom.ker (πT k)) ≠ ⊥)
    (hrank : ∀ k, k ≤ n → Module.finrank 𝒪 (M k) =
      Module.finrank 𝒪 (Submodule.torsionBySet (T k) (M k) ↑(RingHom.ker (πT k))) *
        Module.finrank 𝒪 (T k))

    (hsurjn : ∀ D : GaloisRep.DeformationRingData 𝒪 ρbar (𝒟 n),
      ∃ ψ : D.R →ₐ[𝒪] T n, Function.Surjective ψ ∧ ∃ hψ : IsLocalHom (ψ : D.R →+* T n),
        (D.ρ.baseChangeAlong (ψ : D.R →+* T n) hψ).IsEquiv (ρT n))
    (hTW : ∀ (D : GaloisRep.DeformationRingData 𝒪 ρbar (𝒟 n))
      (φ : D.R →ₐ[𝒪] T n) (hφ : IsLocalHom (φ : D.R →+* T n)),
      (D.ρ.baseChangeAlong (φ : D.R →+* T n) hφ).IsEquiv (ρT n) →
      ∃ r : ℕ, Nonempty (@Algebra.PatchingDatum 𝒪 _ p r D.R _ _ (M n) _
        (Module.compHom (M n) (φ : D.R →+* T n))))

    (hrung : ∀ k, k < n →
      Nonempty (GaloisRep.DeformationRingData 𝒪 ρbar (𝒟 (k + 1))) ∧
      (∀ D' : GaloisRep.DeformationRingData 𝒪 ρbar (𝒟 k),
        ∃ ψ : D'.R →ₐ[𝒪] T k, Function.Surjective ψ ∧ ∃ hψ : IsLocalHom (ψ : D'.R →+* T k),
          (D'.ρ.baseChangeAlong (ψ : D'.R →+* T k) hψ).IsEquiv (ρT k)) ∧
      ∃ c : 𝒪, c ≠ 0 ∧
        (∃ (i : M (k + 1) →ₗ[𝒪] M k) (j : M k →ₗ[𝒪] M (k + 1)) (Δ : T (k + 1)),
          (∀ (m' : M k) (m : M (k + 1)), B (k + 1) (j m') m = B k m' (i m)) ∧
          (∀ m : M (k + 1), j (i m) = Δ • m) ∧
          Ideal.span {πT (k + 1) Δ} = Ideal.span {c} ∧
          Submodule.map i ((Submodule.torsionBySet (T (k + 1)) (M (k + 1))
              ↑(RingHom.ker (πT (k + 1)))).restrictScalars 𝒪) =
            (Submodule.torsionBySet (T k) (M k) ↑(RingHom.ker (πT k))).restrictScalars 𝒪) ∧
        ∀ (D₀ : GaloisRep.DeformationRingData 𝒪 ρbar (𝒟 (k + 1)))
          (D' : GaloisRep.DeformationRingData 𝒪 ρbar (𝒟 k))
          (φ₀ : D₀.R →ₐ[𝒪] T (k + 1)) (hφ₀ : IsLocalHom (φ₀ : D₀.R →+* T (k + 1))),
          (D₀.ρ.baseChangeAlong (φ₀ : D₀.R →+* T (k + 1)) hφ₀).IsEquiv (ρT (k + 1)) →
          (∀ (θ : D'.R →ₐ[𝒪] D₀.R) (hθ : IsLocalHom (θ : D'.R →+* D₀.R)),
            (D'.ρ.baseChangeAlong (θ : D'.R →+* D₀.R) hθ).IsEquiv D₀.ρ →
            Module.length 𝒪 (RingHom.ker (((πT (k + 1)).comp φ₀).comp θ)).Cotangent ≤
              Module.length 𝒪 (RingHom.ker ((πT (k + 1)).comp φ₀)).Cotangent +
                Module.length 𝒪 (𝒪 ⧸ Ideal.span {c})) ∧
          (∀ (φ' : D'.R →ₐ[𝒪] T k) (hφ' : IsLocalHom (φ' : D'.R →+* T k)),
            (D'.ρ.baseChangeAlong (φ' : D'.R →+* T k) hφ').IsEquiv (ρT k) →
            ∀ (θ : D'.R →ₐ[𝒪] D₀.R) (hθ : IsLocalHom (θ : D'.R →+* D₀.R)),
            (D'.ρ.baseChangeAlong (θ : D'.R →+* D₀.R) hθ).IsEquiv D₀.ρ →
            (πT k).comp φ' = ((πT (k + 1)).comp φ₀).comp θ)) :
    ∀ (D : GaloisRep.DeformationRingData 𝒪 ρbar (𝒟 0)) (ρ' : GaloisRepAdic (T 0)),
      𝒟 0 ρ' →
      ρ'.residual.IsEquiv
        (ρbar.baseChangeAlong (IsLocalRing.ResidueField.map (algebraMap 𝒪 (T 0)))) →
      (∃ ψ : D.R →ₐ[𝒪] T 0, Function.Surjective ψ ∧ ∃ hψ : IsLocalHom (ψ : D.R →+* T 0),
        (D.ρ.baseChangeAlong (ψ : D.R →+* T 0) hψ).IsEquiv ρ') →
      ∀ (φ : D.R →ₐ[𝒪] T 0) (hφ : IsLocalHom (φ : D.R →+* T 0)),
        (D.ρ.baseChangeAlong (φ : D.R →+* T 0) hφ).IsEquiv ρ' →
        ∃ (Mx : Type) (_ : AddCommGroup Mx) (_ : Module D.R Mx) (_ : Module (T 0) Mx)
          (_ : Nontrivial Mx),
          (∀ (x : D.R) (m : Mx), φ x • m = x • m) ∧
          ∃ r : ℕ, Nonempty (Algebra.PatchingDatum 𝒪 p r D.R Mx) := by p2m_exact_reverting @_root_.P2MW.S_GaloisRep_DeformationRingData_exists_patchingDatum_of_ladder.solution
