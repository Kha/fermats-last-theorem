import Definitions.Def_ExtCitation_CyclotomicUnits
import P2M.Util
import P2M.Sol.S_ExtCitation_Cyclotomic_unitsOmegaEigenvector_two_eq_zero_of_local_pow
set_option autoImplicit false
namespace ExtCitation.Cyclotomic
open NumberField IsDedekindDomain JacobiSumStickelberger Stickelberger
variable (p : ℕ) [Fact p.Prime]
theorem unitsOmegaEigenvector_two_eq_zero_of_local_pow (hp5 : 5 ≤ p)
    (u : (𝓞 (CyclotomicField p ℚ))ˣ)
    (heig : IsOmegaEigenvector (unitsGalAction p) 2
      (ModP.proj p (Additive (𝓞 (CyclotomicField p ℚ))ˣ) (Additive.ofMul u)))
    (hloc : ∀ 𝔭 : HeightOneSpectrum (𝓞 (CyclotomicField p ℚ)),
      (p : 𝓞 (CyclotomicField p ℚ)) ∈ 𝔭.asIdeal →
      ∃ v : (𝔭.adicCompletion (CyclotomicField p ℚ))ˣ,
        v ^ p = (Units.map (algebraMap (𝓞 (CyclotomicField p ℚ))
          (𝔭.adicCompletion (CyclotomicField p ℚ))).toMonoidHom) u) :
    ModP.proj p (Additive (𝓞 (CyclotomicField p ℚ))ˣ) (Additive.ofMul u) = 0 := by p2m_exact_reverting @_root_.P2MW.S_ExtCitation_Cyclotomic_unitsOmegaEigenvector_two_eq_zero_of_local_pow.solution
