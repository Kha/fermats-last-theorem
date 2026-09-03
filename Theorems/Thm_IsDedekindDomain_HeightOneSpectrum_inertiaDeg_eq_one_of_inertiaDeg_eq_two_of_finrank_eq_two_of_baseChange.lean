import Definitions.Def_DedekindDomain_Completion_BaseChange
import P2M.Util
import P2M.Sol.S_IsDedekindDomain_HeightOneSpectrum_inertiaDeg_eq_one_of_inertiaDeg_eq_two_of_finrank_eq_two_of_baseChange

set_option autoImplicit false

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped Polynomial

theorem IsDedekindDomain.HeightOneSpectrum.inertiaDeg_eq_one_of_inertiaDeg_eq_two_of_finrank_eq_two_of_baseChange
    (K L K' M : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Field K'] [NumberField K']
    [Field M] [NumberField M]
    [Algebra K L] [Algebra K K'] [Algebra K M] [Algebra L M] [Algebra K' M]
    [IsScalarTower K L M] [IsScalarTower K K' M] [IsGalois K L]
    (hL : Module.finrank K L = 2) (hK' : Module.finrank K K' = 2)
    (hdisj : Module.finrank K' M = Module.finrank K L)
    (hcomp : ∀ x : M, x ∈ Algebra.adjoin K' (Set.range (algebraMap L M)))
    (v : HeightOneSpectrum (𝓞 K))
    (hv : ∀ w : v.Extension (𝓞 L), Ideal.ramificationIdx' v.asIdeal w.1.asIdeal = 1)
    (𝔳 : v.Extension (𝓞 K')) (h𝔳 : Ideal.inertiaDeg' v.asIdeal 𝔳.1.asIdeal = 2)
    (𝔴 : 𝔳.1.Extension (𝓞 M)) :
    Ideal.inertiaDeg' 𝔳.1.asIdeal 𝔴.1.asIdeal = 1 := by p2m_exact_reverting @_root_.P2MW.S_IsDedekindDomain_HeightOneSpectrum_inertiaDeg_eq_one_of_inertiaDeg_eq_two_of_finrank_eq_two_of_baseChange.solution
