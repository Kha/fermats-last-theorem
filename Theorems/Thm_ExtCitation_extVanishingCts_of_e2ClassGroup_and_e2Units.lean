import Definitions.Def_ExtCitation_AdmissibleExtension_v2
import Definitions.Def_ExtCitation_CyclotomicUnits
import P2M.Util
import P2M.Sol.S_ExtCitation_extVanishingCts_of_e2ClassGroup_and_e2Units
set_option autoImplicit false
namespace ExtCitation
open NumberField IsDedekindDomain JacobiSumStickelberger Stickelberger
variable (p : ℕ) [Fact p.Prime]
theorem extVanishingCts_of_e2ClassGroup_and_e2Units (hp5 : 5 ≤ p)
    (unitsGalAction' : (ZMod p)ˣ →* Module.End (ZMod p)
      (ModP p (Additive (𝓞 (CyclotomicField p ℚ))ˣ)))
    (hρ : ∀ d u, unitsGalAction' d
        (ModP.proj p _ (Additive.ofMul u)) =
      ModP.proj p _ (Additive.ofMul
        (Units.mapEquiv (clRingAction p (CyclotomicField p ℚ) d).toMulEquiv u)))
    (hE2CL : ∀ a : ClGalModule p (𝓞 (CyclotomicField p ℚ)),
      IsOmegaEigenvector (clGalAction p (CyclotomicField p ℚ)) 2 a → a = 0)
    (hUnitsB2 : ∀ u : (𝓞 (CyclotomicField p ℚ))ˣ,
      IsOmegaEigenvector unitsGalAction' 2
        (ModP.proj p (Additive (𝓞 (CyclotomicField p ℚ))ˣ) (Additive.ofMul u)) →
      (∀ 𝔭 : HeightOneSpectrum (𝓞 (CyclotomicField p ℚ)),
        (p : 𝓞 (CyclotomicField p ℚ)) ∈ 𝔭.asIdeal →
        ∃ v : (𝔭.adicCompletion (CyclotomicField p ℚ))ˣ,
          v ^ p = (Units.map (algebraMap (𝓞 (CyclotomicField p ℚ))
            (𝔭.adicCompletion (CyclotomicField p ℚ))).toMonoidHom) u) →
      ModP.proj p (Additive (𝓞 (CyclotomicField p ℚ))ˣ) (Additive.ofMul u) = 0) :
    ExtVanishingCts p := by p2m_exact_reverting @_root_.P2MW.S_ExtCitation_extVanishingCts_of_e2ClassGroup_and_e2Units.solution
