import Definitions.Def_DedekindDomain_Completion_BaseChange
import P2M.Util
import P2M.Sol.S_IsDedekindDomain_HeightOneSpectrum_exists_valued_eq_exp_inertiaDeg_mul_of_valued_norm_eq_of_baseChange

set_option autoImplicit false

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped Polynomial

theorem IsDedekindDomain.HeightOneSpectrum.exists_valued_eq_exp_inertiaDeg_mul_of_valued_norm_eq_of_baseChange
    (K L K' M : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Field K'] [NumberField K']
    [Field M] [NumberField M]
    [Algebra K L] [Algebra K K'] [Algebra K M] [Algebra L M] [Algebra K' M]
    [IsScalarTower K L M] [IsScalarTower K K' M] [IsGalois K L]
    (hdisj : Module.finrank K' M = Module.finrank K L)
    (hcomp : ∀ x : M, x ∈ Algebra.adjoin K' (Set.range (algebraMap L M)))
    (hdeg : (Module.finrank K L).Prime) (hK' : Module.finrank K K' = 2)
    (v : HeightOneSpectrum (𝓞 K))
    (hv : ∀ w : v.Extension (𝓞 L), Ideal.ramificationIdx' v.asIdeal w.1.asIdeal = 1)
    (𝔳 : v.Extension (𝓞 K')) (𝔴 : 𝔳.1.Extension (𝓞 M))
    (x : 𝔳.1.adicCompletion K') (hx : x ≠ 0)
    (hdiv : ∃ k : ℤ, Valued.v (Algebra.norm (v.adicCompletion K) x) =
      ((Multiplicative.ofAdd ((Module.finrank K L : ℤ) * k) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) :
    ∃ k : ℤ, Valued.v x = WithZero.exp ((Ideal.inertiaDeg' 𝔳.1.asIdeal 𝔴.1.asIdeal : ℤ) * k) := by p2m_exact_reverting @_root_.P2MW.S_IsDedekindDomain_HeightOneSpectrum_exists_valued_eq_exp_inertiaDeg_mul_of_valued_norm_eq_of_baseChange.solution
