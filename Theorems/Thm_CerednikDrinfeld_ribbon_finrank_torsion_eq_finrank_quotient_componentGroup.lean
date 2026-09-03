import Mathlib
import Definitions.Def_ModularCurve_HeckeCarrier
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_ribbon_finrank_torsion_eq_finrank_quotient_componentGroup
set_option autoImplicit false
open ModularCurve

theorem CerednikDrinfeld.ribbon_finrank_torsion_eq_finrank_quotient_componentGroup
    {E V : Type*} [Fintype E] [Fintype V] [DecidableEq V] {D : DegeneracyData E V}
    (H : HeckeData D)
    (Tadj : Nat.Primes → (ribbonKernel D →ₗ[ℤ] ribbonKernel D))
    (hadjK : ∀ (ℓ : Nat.Primes) (x y : ribbonKernel D),
      ribbonGram D (Tadj ℓ x) y = ribbonGram D x (heckeKernelMap H ℓ y))
    (hadjK' : ∀ (ℓ : Nat.Primes) (x y : ribbonKernel D),
      ribbonGram D (heckeKernelMap H ℓ x) y = ribbonGram D x (Tadj ℓ y))
    {Ψmod : Type*} [AddCommGroup Ψmod] [Module HeckeAlg Ψmod]
    (eΨ : Ψmod ≃+ ribbonComponentGroup D)
    (hΨ : ∀ (ℓ : Nat.Primes) (c : Ψmod), eΨ (heckeGen ℓ • c) =
      ribbonComponentGroupMap D (Tadj ℓ) (heckeKernelMap H ℓ) (hadjK ℓ) (eΨ c))
    {Ψamod : Type*} [AddCommGroup Ψamod] [Module HeckeAlg Ψamod]
    (eΨa : Ψamod ≃+ ribbonComponentGroup D)
    (hΨa : ∀ (ℓ : Nat.Primes) (c : Ψamod), eΨa (heckeGen ℓ • c) =
      ribbonComponentGroupMap D (heckeKernelMap H ℓ) (Tadj ℓ) (hadjK' ℓ) (eΨa c))
    (𝔪 : Ideal HeckeAlg) [𝔪.IsMaximal] :
    Module.finrank (HeckeAlg ⧸ 𝔪) ↥(heckeTorsion Ψmod 𝔪) =
      Module.finrank (HeckeAlg ⧸ 𝔪) (Ψamod ⧸ (𝔪 • (⊤ : Submodule HeckeAlg Ψamod))) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_ribbon_finrank_torsion_eq_finrank_quotient_componentGroup.solution
