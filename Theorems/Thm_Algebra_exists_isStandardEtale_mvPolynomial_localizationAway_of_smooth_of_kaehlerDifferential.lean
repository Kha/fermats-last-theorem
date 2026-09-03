import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_exists_isStandardEtale_mvPolynomial_localizationAway_of_smooth_of_kaehlerDifferential

set_option autoImplicit false

open Topology

theorem Algebra.exists_isStandardEtale_mvPolynomial_localizationAway_of_smooth_of_kaehlerDifferential
    (S : Type) [CommRing S] [IsDomain S] [Algebra ℂ S] [Algebra.FiniteType ℂ S] (hsm : Algebra.Smooth ℂ S)
    {n : ℕ} (hrank : Module.rank S (KaehlerDifferential ℂ S) = n)
    (σ₀ : S →ₐ[ℂ] ℂ) (t : Fin n → S)
    (hdt : (RingHom.ker σ₀.toRingHom) • (⊤ : Submodule S (KaehlerDifferential ℂ S)) ⊔
        Submodule.span S (Set.range fun i : Fin n => KaehlerDifferential.D ℂ S (t i)) = ⊤) :
    ∃ g : S, σ₀ g ≠ 0 ∧
      letI : Algebra (MvPolynomial (Fin n) ℂ) (Localization.Away g) :=
        ((algebraMap S (Localization.Away g)).comp (MvPolynomial.aeval t).toRingHom).toAlgebra
      Algebra.IsStandardEtale (MvPolynomial (Fin n) ℂ) (Localization.Away g) := by p2m_exact_reverting @_root_.P2MW.S_Algebra_exists_isStandardEtale_mvPolynomial_localizationAway_of_smooth_of_kaehlerDifferential.solution
