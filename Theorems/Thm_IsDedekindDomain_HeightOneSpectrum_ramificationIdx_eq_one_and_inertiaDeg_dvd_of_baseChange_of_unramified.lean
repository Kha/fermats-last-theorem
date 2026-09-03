import Definitions.Def_DedekindDomain_Completion_BaseChange
import P2M.Util
import P2M.Sol.S_IsDedekindDomain_HeightOneSpectrum_ramificationIdx_eq_one_and_inertiaDeg_dvd_of_baseChange_of_unramified

set_option autoImplicit false

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped Polynomial

theorem IsDedekindDomain.HeightOneSpectrum.ramificationIdx_eq_one_and_inertiaDeg_dvd_of_baseChange_of_unramified
    (K L K' M : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Field K'] [NumberField K']
    [Field M] [NumberField M]
    [Algebra K L] [Algebra K K'] [Algebra K M] [Algebra L M] [Algebra K' M]
    [IsScalarTower K L M] [IsScalarTower K K' M] [IsGalois K L]
    (hdisj : Module.finrank K' M = Module.finrank K L)
    (hcomp : ∀ x : M, x ∈ Algebra.adjoin K' (Set.range (algebraMap L M)))
    (v : HeightOneSpectrum (𝓞 K))
    (hv : ∀ w : v.Extension (𝓞 L), Ideal.ramificationIdx' v.asIdeal w.1.asIdeal = 1)
    (𝔳 : v.Extension (𝓞 K')) (𝔴 : 𝔳.1.Extension (𝓞 M)) :
    Ideal.ramificationIdx' 𝔳.1.asIdeal 𝔴.1.asIdeal = 1 ∧
      Ideal.inertiaDeg' 𝔳.1.asIdeal 𝔴.1.asIdeal ∣ Module.finrank K L := by p2m_exact_reverting @_root_.P2MW.S_IsDedekindDomain_HeightOneSpectrum_ramificationIdx_eq_one_and_inertiaDeg_dvd_of_baseChange_of_unramified.solution
