import Definitions.Def_ExtCitation_CyclotomicUnits
import P2M.Util
import P2M.Sol.S_ExtCitation_Cyclotomic_omegaIdempotent_two_cycloUnitTwo_ne_zero
set_option autoImplicit false
namespace ExtCitation.Cyclotomic
open NumberField IsDedekindDomain JacobiSumStickelberger Stickelberger
variable (p : ℕ) [Fact p.Prime]
theorem omegaIdempotent_two_cycloUnitTwo_ne_zero (hp5 : 5 ≤ p)
    (ζ : 𝓞 (CyclotomicField p ℚ)) (hζ : IsPrimitiveRoot (ζ : CyclotomicField p ℚ) p)
    (c₂ : (𝓞 (CyclotomicField p ℚ))ˣ) (hc : (c₂ : 𝓞 (CyclotomicField p ℚ)) = 1 + ζ) :
    omegaIdempotent p (unitsGalAction p) 2
        (ModP.proj p (Additive (𝓞 (CyclotomicField p ℚ))ˣ)
          (Additive.ofMul c₂)) ≠ 0 := by p2m_exact_reverting @_root_.P2MW.S_ExtCitation_Cyclotomic_omegaIdempotent_two_cycloUnitTwo_ne_zero.solution
