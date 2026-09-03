import Definitions.Def_DedekindDomain_Completion_BaseChange
import P2M.Util
import P2M.Sol.S_IsDedekindDomain_HeightOneSpectrum_exists_unique_extension_and_algEquiv_adjoinRoot_of_not_isSquare

set_option autoImplicit false

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped Polynomial

theorem IsDedekindDomain.HeightOneSpectrum.exists_unique_extension_and_algEquiv_adjoinRoot_of_not_isSquare
    (K K' : Type) [Field K] [NumberField K] [Field K'] [NumberField K'] [Algebra K K']
    (hdeg : Module.finrank K K' = 2)
    (d : K) (r : K') (hr : r ^ 2 = algebraMap K K' d) (hgen : Algebra.adjoin K {r} = ⊤)
    (v : HeightOneSpectrum (𝓞 K))
    (hd : ¬ IsSquare (algebraMap K (v.adicCompletion K) d)) :
    (∀ 𝔳 𝔳' : v.Extension (𝓞 K'), 𝔳 = 𝔳') ∧
    ∀ 𝔳 : v.Extension (𝓞 K'),
      Nonempty (𝔳.1.adicCompletion K' ≃ₐ[v.adicCompletion K]
        AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C (algebraMap K (v.adicCompletion K) d))) := by p2m_exact_reverting @_root_.P2MW.S_IsDedekindDomain_HeightOneSpectrum_exists_unique_extension_and_algEquiv_adjoinRoot_of_not_isSquare.solution
