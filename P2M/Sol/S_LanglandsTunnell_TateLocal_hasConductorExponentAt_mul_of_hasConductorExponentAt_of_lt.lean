import Definitions.Def_LanglandsTunnell_TateLocalConstantsAt
import P2M.Util
namespace P2MW.S_LanglandsTunnell_TateLocal_hasConductorExponentAt_mul_of_hasConductorExponentAt_of_lt

set_option autoImplicit false

open NumberField NumberField.AdelicLevel IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

open LanglandsTunnell.TateLocal in
theorem solution
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (lam nu : (v.adicCompletion K)ˣ →* ℂˣ) (a b : ℕ)
    (hlam : HasConductorExponentAt K v lam a) (hnu : HasConductorExponentAt K v nu b) (hlt : b < a) :
    HasConductorExponentAt K v (lam * nu) a := by
  obtain ⟨hlamTriv, hlamNontriv⟩ := hlam
  obtain ⟨hnuTriv, -⟩ := hnu
  refine ⟨fun u hu => ?_, fun m hm => ?_⟩
  ·
    rw [MonoidHom.mul_apply, hlamTriv u hu, hnuTriv u (higherUnitsAt_antitone K v hlt.le hu), one_mul]
  · rcases le_or_gt b m with hbm | hmb
    ·
      obtain ⟨u, hu, hne⟩ := hlamNontriv m hm
      exact ⟨u, hu, by rwa [MonoidHom.mul_apply, hnuTriv u (higherUnitsAt_antitone K v hbm hu), mul_one]⟩
    ·
      obtain ⟨u, hu, hne⟩ := hlamNontriv b hlt
      exact ⟨u, higherUnitsAt_antitone K v hmb.le hu, by rwa [MonoidHom.mul_apply, hnuTriv u hu, mul_one]⟩
