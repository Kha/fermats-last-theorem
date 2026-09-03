import Definitions.Def_CuspForm_TWLevelHeckeModule
import P2M.Util
import P2M.Sol.S_CuspForm_TWLevel_exists_linearMap_ML_HQ_HR_surjective_and_ker_eq_span

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

open IsLocalRing CuspForm.TWLevel

theorem CuspForm.TWLevel.exists_linearMap_ML_HQ_HR_surjective_and_ker_eq_span
    {𝒪 : Type} [CommRing 𝒪] [IsLocalRing 𝒪]
    (p : ℕ) (S : Set ℕ) (N : ℕ) [NeZero N] (r : ℕ) [NeZero r] (hr4 : 4 ≤ r)
    (θ : CuspForm.heckeAlgebra N 2 S →+* ResidueField 𝒪)
    {t : ℕ} (qv : Fin t → ℕ) [∀ i, NeZero (qv i)]
    (α : Fin t → ResidueField 𝒪)
    (πΔ : ∀ i, (ZMod (qv i))ˣ →* Multiplicative (ZMod (p ^ padicValNat p (qv i - 1))))

    (hcQ : OpComm N r qv S 𝒪 (HQ N r qv p πΔ)) (hdc : DiaComm N r qv S 𝒪 (HQ N r qv p πΔ))
    (hcR : OpComm N r qv S 𝒪 (HR N r qv)) :
    ∃ lam₀ : ML N r qv S 𝒪 (HQ N r qv p πΔ) θ α hcQ →ₗ[𝒪] ML N r qv S 𝒪 (HR N r qv) θ α hcR,

      Function.Surjective lam₀ ∧

      (∀ (g : Gen (level N r qv) S t) (x : ML N r qv S 𝒪 (HQ N r qv p πΔ) θ α hcQ),
        lam₀ ((MvPolynomial.X g : (heckeData N r qv S 𝒪 (HQ N r qv p πΔ) θ α hcQ).FreeAlg) • x) =
          (MvPolynomial.X g : (heckeData N r qv S 𝒪 (HR N r qv) θ α hcR).FreeAlg) • lam₀ x) ∧

      (∀ u ∈ HR N r qv, ∀ x : ML N r qv S 𝒪 (HQ N r qv p πΔ) θ α hcQ,
        lam₀ (diaML N r qv S 𝒪 (HQ N r qv p πΔ) θ α hcQ hdc u x) = lam₀ x) ∧

      (∀ x : ML N r qv S 𝒪 (HQ N r qv p πΔ) θ α hcQ,
        lam₀ x = 0 ↔ x ∈ Submodule.span 𝒪
          {y : ML N r qv S 𝒪 (HQ N r qv p πΔ) θ α hcQ |
            ∃ u ∈ HR N r qv, ∃ z : ML N r qv S 𝒪 (HQ N r qv p πΔ) θ α hcQ,
              y = diaML N r qv S 𝒪 (HQ N r qv p πΔ) θ α hcQ hdc u z - z}) := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_TWLevel_exists_linearMap_ML_HQ_HR_surjective_and_ker_eq_span.solution
