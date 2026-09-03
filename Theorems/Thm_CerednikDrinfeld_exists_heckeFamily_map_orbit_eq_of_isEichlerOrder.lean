import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_exists_heckeFamily_map_orbit_eq_of_isEichlerOrder

set_option autoImplicit false

open scoped MatrixGroups Topology Quaternion TensorProduct NumberField
open IsDedekindDomain QuaternionAlgebra CerednikDrinfeld

theorem CerednikDrinfeld.exists_heckeFamily_map_orbit_eq_of_isEichlerOrder
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] {N : ℕ} [NeZero N]
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ R : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) (hR : IsEichlerOrder R N) (hRΛ : R ≤ Λ)
    (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ) (hι : Function.Injective ι) :
    ∃ H : ∀ ℓ : ℕ, ℓ.Prime → Multiset (GL (Fin 2) ℝ),
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ∃ S : Finset ℍ[ℚ, a, b],
        (∀ x ∈ S, x ∈ R ∧ nrd x = ℓ ∧
          ∃ h ∈ (if ℓ ∣ N then levelHeckeUSet Λ R ℓ else primeHeckeSet R ℓ),
            (h : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) = x ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ)) ∧
        (∀ y : ℍ[ℚ, a, b], y ∈ R → nrd y = ℓ →
          (∃ h ∈ (if ℓ ∣ N then levelHeckeUSet Λ R ℓ else primeHeckeSet R ℓ),
            (h : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) = y ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ)) →
          ∃! x, x ∈ S ∧ ∃ u : ℍ[ℚ, a, b], IsUnitOf R u ∧ nrd u = 1 ∧ u * x = y) ∧
        (H ℓ hℓ).map (fun g => (g : Matrix (Fin 2) (Fin 2) ℝ)) = S.val.map ι) ∧
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ∀ γ ∈ fuchsianGroup R ι, ∀ τ : UpperHalfPlane,
        ((H ℓ hℓ).map fun δ => MulAction.orbit ↥(fuchsianGroup R ι) (δ • γ • τ)) =
          ((H ℓ hℓ).map fun δ => MulAction.orbit ↥(fuchsianGroup R ι) (δ • τ))) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_exists_heckeFamily_map_orbit_eq_of_isEichlerOrder.solution
