import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_exists_isStandardEtale_polynomial_localizationAway_of_smooth_of_kaehlerDifferential

set_option autoImplicit false

open Topology Polynomial

theorem Algebra.exists_isStandardEtale_polynomial_localizationAway_of_smooth_of_kaehlerDifferential
    (S : Type) [CommRing S] [IsDomain S] [Algebra ℂ S] [Algebra.FiniteType ℂ S] (hsm : Algebra.Smooth ℂ S)
    (hrank : Module.rank S (KaehlerDifferential ℂ S) = 1)
    (σ₀ : S →ₐ[ℂ] ℂ) (t : S)
    (hdt : KaehlerDifferential.D ℂ S t ∉ (RingHom.ker σ₀.toRingHom) • (⊤ : Submodule S (KaehlerDifferential ℂ S))) :
    ∃ (g : S), σ₀ g ≠ 0 ∧
      letI : Algebra (Polynomial ℂ) (Localization.Away g) :=
        ((algebraMap S (Localization.Away g)).comp (Polynomial.aeval t).toRingHom).toAlgebra
      Algebra.IsStandardEtale (Polynomial ℂ) (Localization.Away g) := by p2m_exact_reverting @_root_.P2MW.S_Algebra_exists_isStandardEtale_polynomial_localizationAway_of_smooth_of_kaehlerDifferential.solution
