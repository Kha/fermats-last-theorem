import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import P2M.Util
namespace P2MW.S_LanglandsTunnell_TateLocal_hasConductorExponentAt_mul_of_hasConductorExponentAt_zero

set_option autoImplicit false

open NumberField NumberField.StandardAddChar NumberField.AdelicLevel IsDedekindDomain

namespace LanglandsTunnell
namespace TateLocal
p2m_export "LanglandsTunnell.TateLocal" "higherUnitsAt higherUnitsAt_antitone HasConductorExponentAt"
p2m_open "LanglandsTunnell.TateLocal LanglandsTunnell"

theorem apply_eq_one_of_hasConductorExponentAt_zero
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (RingOfIntegers K))
    (ω : (v.adicCompletion K)ˣ →* ℂˣ) (hω : HasConductorExponentAt K v ω 0)
    (m : ℕ) (u : (v.adicCompletion K)ˣ) (hu : u ∈ higherUnitsAt K v m) : ω u = 1 :=
  hω.1 u (higherUnitsAt_antitone K v (Nat.zero_le m) hu)

end LanglandsTunnell.TateLocal

open _root_.LanglandsTunnell.TateLocal _root_.P2MW.S_LanglandsTunnell_TateLocal_hasConductorExponentAt_mul_of_hasConductorExponentAt_zero.LanglandsTunnell.TateLocal in
theorem solution
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (RingOfIntegers K))
    (χ ω : (v.adicCompletion K)ˣ →* ℂˣ) (c : ℕ) (hχ : HasConductorExponentAt K v χ c)
    (hω : HasConductorExponentAt K v ω 0) :
    HasConductorExponentAt K v (χ * ω) c := by
  refine ⟨fun u hu => ?_, fun m hm => ?_⟩
  · rw [MonoidHom.mul_apply, hχ.1 u hu, apply_eq_one_of_hasConductorExponentAt_zero K v ω hω c u hu, one_mul]
  · obtain ⟨u, hu, hne⟩ := hχ.2 m hm
    refine ⟨u, hu, ?_⟩
    rw [MonoidHom.mul_apply, apply_eq_one_of_hasConductorExponentAt_zero K v ω hω m u hu, mul_one]
    exact hne
