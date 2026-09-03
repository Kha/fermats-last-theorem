import Mathlib
import Definitions.Def_ArtinL_Abelian
import P2M.Util
import P2M.Sol.S_ArtinL_Abelian_factorization_absNorm_conductor_eq_finsum_inertiaDeg_mul_conductorExponent

set_option autoImplicit false

open NumberField
open scoped Classical in

theorem ArtinL.Abelian.factorization_absNorm_conductor_eq_finsum_inertiaDeg_mul_conductorExponent
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (ψ : (L ≃ₐ[K] L) →* ℂˣ) (p : ℕ) (hp : p.Prime) :
    (Ideal.absNorm (ArtinL.Abelian.conductor ψ)).factorization p =
      ∑ᶠ w : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
        if ((p : ℕ) : 𝓞 K) ∈ w.asIdeal then
          (Ideal.span {(p : ℤ)}).inertiaDeg' w.asIdeal * ArtinL.Abelian.conductorExponent ψ w
        else 0 := by p2m_exact_reverting @_root_.P2MW.S_ArtinL_Abelian_factorization_absNorm_conductor_eq_finsum_inertiaDeg_mul_conductorExponent.solution
