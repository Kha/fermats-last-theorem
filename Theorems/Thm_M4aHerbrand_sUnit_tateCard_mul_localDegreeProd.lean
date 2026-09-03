import Mathlib.RingTheory.DedekindDomain.SInteger
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification
import Mathlib.NumberTheory.NumberField.Units.Basic
import Mathlib.NumberTheory.Divisors
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.GroupTheory.Torsion
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.GroupTheory.Perm.Cycle.Basic
import P2M.Util
import P2M.Sol.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd
attribute [-simp] M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq

set_option autoImplicit false
open NumberField IsDedekindDomain

theorem M4aHerbrand.sUnit_tateCard_mul_localDegreeProd
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hσ : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (S : Finset (HeightOneSpectrum (𝓞 K)))

    (W : Set (HeightOneSpectrum (𝓞 L))) (hW : W = {w | w.under (𝓞 K) ∈ ↑S})

    (Φ : ↥(W.unit L) ≃* ↥(W.unit L))
    (hΦ : ∀ u, (((Φ u : Lˣ) : L)) = σ (((u : Lˣ) : L)))

    (d : Additive ↥(W.unit L) →+ Additive ↥(W.unit L))
    (hd : ∀ u, d (Additive.ofMul u) = Additive.ofMul (Φ u) - Additive.ofMul u)
    (N : Additive ↥(W.unit L) →+ Additive ↥(W.unit L))
    (hN : ∀ u, N (Additive.ofMul u)
          = ∑ i ∈ Finset.range (Nat.card (L ≃ₐ[K] L)), Additive.ofMul ((Φ ^ i) u))

    (sf : HeightOneSpectrum (𝓞 K) → ℕ)
    (hsf : ∀ v, sf v = Nat.card {w : HeightOneSpectrum (𝓞 L) // w.under (𝓞 K) = v})
    (si : InfinitePlace K → ℕ)
    (hsi : ∀ v, si v = Nat.card {w : InfinitePlace L // InfinitePlace.comap w (algebraMap K L) = v}) :
    Nat.card (↥d.ker ⧸ N.range.addSubgroupOf d.ker) * Nat.card (L ≃ₐ[K] L)
        = ((∏ v ∈ S, Nat.card (L ≃ₐ[K] L) / sf v)
            * ∏ v : InfinitePlace K, Nat.card (L ≃ₐ[K] L) / si v)
          * Nat.card (↥N.ker ⧸ d.range.addSubgroupOf N.ker)
      ∧ Nat.card (↥d.ker ⧸ N.range.addSubgroupOf d.ker) ≠ 0 := by p2m_exact_reverting @_root_.P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd.solution
