import Definitions.Def_CuspForm_HeckeGaloisRepDatum
import P2M.Util
import P2M.Sol.S_CuspForm_HeckeGaloisRepDatum_exists_points_jointly_injective
attribute [-simp] PowerSeries.coeff_heckeV PowerSeries.coeff_heckeU

variable {N : ℕ} [NeZero N] {S : Finset ℕ}
  {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
  [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
  {θ : CuspForm.heckeAlgebra N 2 (↑S : Set ℕ) →+* IsLocalRing.ResidueField 𝒪}
  {T : Type} [CommRing T] [IsLocalRing T] [IsNoetherianRing T]
  [IsAdicComplete (IsLocalRing.maximalIdeal T) T] [Algebra 𝒪 T] [IsLocalHom (algebraMap 𝒪 T)]
  [Module.Finite 𝒪 T] [Module.Free 𝒪 T]

theorem CuspForm.HeckeGaloisRepDatum.exists_points_jointly_injective
    [Finite (IsLocalRing.ResidueField 𝒪)] [CharZero 𝒪]
    (hNS : ∀ q : ℕ, q.Prime → q ∣ N → q ∈ S)
    (H : CuspForm.HeckeGaloisRepDatum N (↑S : Set ℕ) 𝒪 θ T) :
    ∃ (n : ℕ) (A : Fin n → Type) (_ : ∀ i, CommRing (A i)) (_ : ∀ i, IsDomain (A i))
      (_ : ∀ i, IsDiscreteValuationRing (A i))
      (_ : ∀ i, IsAdicComplete (IsLocalRing.maximalIdeal (A i)) (A i))
      (_ : ∀ i, Finite (IsLocalRing.ResidueField (A i))) (_ : ∀ i, CharZero (A i))
      (_ : ∀ i, Algebra 𝒪 (A i)) (_ : ∀ i, Module.Finite 𝒪 (A i))
      (_ : ∀ i, IsLocalHom (algebraMap 𝒪 (A i)))
      (χ : ∀ i, T →ₐ[𝒪] A i),
      (∀ i, IsLocalHom (χ i).toRingHom) ∧ (∀ x : T, (∀ i, χ i x = 0) → x = 0) := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_HeckeGaloisRepDatum_exists_points_jointly_injective.solution
