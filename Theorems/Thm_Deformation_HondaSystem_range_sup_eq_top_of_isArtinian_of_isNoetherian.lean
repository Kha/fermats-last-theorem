import Mathlib
import Definitions.Def_Dieudonne_DatumAndHonda
import P2M.Util
import P2M.Sol.S_Deformation_HondaSystem_range_sup_eq_top_of_isArtinian_of_isNoetherian

universe u v

theorem Deformation.HondaSystem.range_sup_eq_top_of_isArtinian_of_isNoetherian
    {S : Type u} [CommRing S] {D : Type v} [AddCommGroup D] [Module S D]
    [IsArtinian S D] [IsNoetherian S D]
    {σ τ : S →+* S} [RingHomSurjective σ] [RingHomSurjective τ]
    (F : D →ₛₗ[σ] D) (V : D →ₛₗ[τ] D) (ℓ : S) (hFV : ∀ x, F (V x) = ℓ • x)
    (L : Submodule S D)
    (sh1 : ∀ x ∈ L, x ∈ LinearMap.range F → ∃ y ∈ L, x = ℓ • y)
    (sh3 : ∀ x ∈ L, V x = 0 → x = 0)
    (hkerF : LinearMap.ker F ≤ LinearMap.range V)
    (htors : ∀ x : D, ℓ • x = 0 → ∃ y ∈ L, ∃ z : D, V z = 0 ∧ y + z = x) :
    LinearMap.range F ⊔ L = ⊤ := by p2m_exact_reverting @_root_.P2MW.S_Deformation_HondaSystem_range_sup_eq_top_of_isArtinian_of_isNoetherian.solution
