import Mathlib
import Definitions.Def_DedekindDomain_IntegralClosure
import P2M.Util
import P2M.Sol.S_IsDedekindDomain_HeightOneSpectrum_finprod_eq_finprod_prod_extension

set_option autoImplicit false

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

theorem IsDedekindDomain.HeightOneSpectrum.finprod_eq_finprod_prod_extension
    (E : Type) [Field E] [NumberField E] (M : Type) [Field M] [NumberField M] [Algebra E M]
    {A : Type} [CommMonoid A] (g : HeightOneSpectrum (𝓞 M) → A) (hg : (Function.mulSupport g).Finite) :
    ∏ᶠ w : HeightOneSpectrum (𝓞 M), g w =
      ∏ᶠ v : HeightOneSpectrum (𝓞 E),
        (letI := Extension.fintype (𝓞 E) E M (𝓞 M) v; ∏ w : v.Extension (𝓞 M), g w.1) := by p2m_exact_reverting @_root_.P2MW.S_IsDedekindDomain_HeightOneSpectrum_finprod_eq_finprod_prod_extension.solution
