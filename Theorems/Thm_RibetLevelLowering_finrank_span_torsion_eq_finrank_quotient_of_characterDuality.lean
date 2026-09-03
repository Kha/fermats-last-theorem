import Mathlib
import Definitions.Def_HeckeGalois_EichlerShimura
import P2M.Util
import P2M.Sol.S_RibetLevelLowering_finrank_span_torsion_eq_finrank_quotient_of_characterDuality
set_option autoImplicit false
open ModularCurve

theorem RibetLevelLowering.finrank_span_torsion_eq_finrank_quotient_of_characterDuality
    {J : Type*} [AddCommGroup J] [Module HeckeAlg J]
    (𝒯 : Submodule HeckeAlg J) (𝔪 : Ideal HeckeAlg) [𝔪.IsMaximal]
    {p : ℕ} (hp : p.Prime) (hpm : (p : HeckeAlg) ∈ 𝔪)
    {L : Type*} [AddCommGroup L] [Module HeckeAlg L] [Module.Finite ℤ L]
    {μ : Type*} [AddCommGroup μ] (hμ : Nat.card μ = p)
    (ε : ↥(𝒯 ⊓ Submodule.torsionBy HeckeAlg J (p : HeckeAlg)) ≃+ (L →+ μ))
    (hε : ∀ (ℓ : Nat.Primes) (y : ↥(𝒯 ⊓ Submodule.torsionBy HeckeAlg J (p : HeckeAlg))) (l : L),
      ε (heckeGen ℓ • y) l = ε y (heckeGen ℓ • l)) :
    Module.finrank (HeckeAlg ⧸ 𝔪)
        ↥(Submodule.span (HeckeAlg ⧸ 𝔪)
          ((Subtype.val : ↥(heckeTorsion J 𝔪) → J) ⁻¹' (𝒯 : Set J))) =
      Module.finrank (HeckeAlg ⧸ 𝔪) (L ⧸ (𝔪 • (⊤ : Submodule HeckeAlg L))) := by p2m_exact_reverting @_root_.P2MW.S_RibetLevelLowering_finrank_span_torsion_eq_finrank_quotient_of_characterDuality.solution
