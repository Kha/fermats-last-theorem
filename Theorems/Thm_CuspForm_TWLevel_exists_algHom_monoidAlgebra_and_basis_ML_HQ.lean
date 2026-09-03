import Definitions.Def_CuspForm_TWLevelHeckeModule
import P2M.Util
import P2M.Sol.S_CuspForm_TWLevel_exists_algHom_monoidAlgebra_and_basis_ML_HQ
attribute [-instance] IharaLemma.IdempotentSplitting.isScalarTower_base_cornerModule IharaLemma.IdempotentSplitting.isScalarTower_base_cornerRing IharaLemma.IdempotentSplitting.algebraBaseCornerRing IharaLemma.IdempotentSplitting.smulCornerModule IharaLemma.IdempotentSplitting.moduleCornerModule IharaLemma.IdempotentSplitting.isLocalRing_cornerRing IharaLemma.IdempotentSplitting.coeOutCornerRing IharaLemma.IdempotentSplitting.isMaximal_𝔪 IharaLemma.IdempotentSplitting.isScalarTower_cornerModule IharaLemma.IdempotentSplitting.isLocalization_cornerRing
attribute [-simp] IharaLemma.IdempotentSplitting.cornerRingLinearEquiv_apply IharaLemma.IdempotentSplitting.cornerRingLinearEquiv_symm_apply IharaLemma.IdempotentSplitting.coe_cornerSmul IharaLemma.IdempotentSplitting.mk.injEq IharaLemma.IdempotentSplitting.mk.sizeOf_spec IharaLemma.IdempotentSplitting.coe_toCornerRing IharaLemma.toCorner_apply

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

open IsLocalRing CuspForm.TWLevel

theorem CuspForm.TWLevel.exists_algHom_monoidAlgebra_and_basis_ML_HQ
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (maximalIdeal 𝒪) 𝒪] [CharZero 𝒪]
    (p : ℕ) [Fact p.Prime] (hp𝒪 : (p : 𝒪) ∈ maximalIdeal 𝒪)

    (S : Set ℕ) (N : ℕ) [NeZero N] (hNS : ∀ q : ℕ, q.Prime → q ∣ N → q ∈ S)

    (r : ℕ) [NeZero r] (hr : r.Prime) (hr4 : 4 ≤ r)

    (θ : CuspForm.heckeAlgebra N 2 S →+* ResidueField 𝒪)

    {t : ℕ} (qv : Fin t → ℕ) [∀ i, NeZero (qv i)] (hqinj : Function.Injective qv)
    (hq : ∀ i, (qv i).Prime ∧ qv i ∉ S) (hqr : ∀ i, qv i ≠ r)
    (α : Fin t → ResidueField 𝒪)

    (πΔ : ∀ i, (ZMod (qv i))ˣ →* Multiplicative (ZMod (p ^ padicValNat p (qv i - 1))))
    (hπΔ : ∀ i, Function.Surjective (πΔ i))

    (hEis : ∃ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S) (hℓL : ¬ ℓ ∣ level N r qv),
      ℓ ≡ 1 [MOD level N r qv] ∧
      θ (CuspForm.heckeAlgebra.T hℓ (not_dvd_of_not_dvd_level N r qv hℓL) hℓS) ≠
        (ℓ : ResidueField 𝒪) + 1)

    (hcQ : OpComm N r qv S 𝒪 (HQ N r qv p πΔ)) (hdc : DiaComm N r qv S 𝒪 (HQ N r qv p πΔ))
    (hcR : OpComm N r qv S 𝒪 (HR N r qv)) :
    ∃ D : MonoidAlgebra 𝒪 (Delta qv p) →ₐ[𝒪]
        Module.End 𝒪 (ML N r qv S 𝒪 (HQ N r qv p πΔ) θ α hcQ),

      (∀ u ∈ HR N r qv, D (MonoidAlgebra.of 𝒪 (Delta qv p) (piQ N r qv p πΔ u)) =
        diaML N r qv S 𝒪 (HQ N r qv p πΔ) θ α hcQ hdc u) ∧

      (∀ δ : Delta qv p, ∃ u ∈ HR N r qv, piQ N r qv p πΔ u = δ) ∧

      Module.Finite 𝒪 (ML N r qv S 𝒪 (HQ N r qv p πΔ) θ α hcQ) ∧

      ∃ b : Fin (Module.finrank 𝒪 (ML N r qv S 𝒪 (HR N r qv) θ α hcR)) →
          ML N r qv S 𝒪 (HQ N r qv p πΔ) θ α hcQ,
        (∀ x : ML N r qv S 𝒪 (HQ N r qv p πΔ) θ α hcQ,
          ∃ c : Fin (Module.finrank 𝒪 (ML N r qv S 𝒪 (HR N r qv) θ α hcR)) →
              MonoidAlgebra 𝒪 (Delta qv p),
            x = ∑ i, D (c i) (b i)) ∧
        (∀ c : Fin (Module.finrank 𝒪 (ML N r qv S 𝒪 (HR N r qv) θ α hcR)) →
            MonoidAlgebra 𝒪 (Delta qv p),
          ∑ i, D (c i) (b i) = 0 ↔ ∀ i, c i = 0) := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_TWLevel_exists_algHom_monoidAlgebra_and_basis_ML_HQ.solution
