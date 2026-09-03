import Definitions.Def_ClassGroup_GaloisAction
import Definitions.Def_Stickelberger_Basic
import P2M.Util
import P2M.Sol.S_ExtCitation_Cyclotomic_thaine_relation_plusField
attribute [-instance] ExtCitation.Cyclotomic.instIsCycExt
attribute [-simp] ExtCitation.Cyclotomic.unitsEnd_proj
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ExtCitation.Cyclotomic
open NumberField JacobiSumStickelberger Stickelberger
variable (p : ℕ) [Fact p.Prime]
theorem thaine_relation_plusField (hp5 : 5 ≤ p)
    (Kplus : Type*) [Field Kplus] [NumberField Kplus] [IsTotallyReal Kplus]
    [Algebra Kplus (CyclotomicField p ℚ)]
    (hKplus : Module.finrank Kplus (CyclotomicField p ℚ) = 2)
    (Δact : (ZMod p)ˣ →* (𝓞 Kplus) ≃+* (𝓞 Kplus))
    (hΔact : ∀ d, (algebraMap (𝓞 Kplus) (𝓞 (CyclotomicField p ℚ))).comp
      (Δact d).toRingHom = (clRingAction p (CyclotomicField p ℚ) d).toRingHom.comp
        (algebraMap (𝓞 Kplus) (𝓞 (CyclotomicField p ℚ))))
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓp : ℓ ≠ p)
    (𝔏 : Ideal (𝓞 Kplus)) (h𝔏max : 𝔏.IsMaximal)
    (h𝔏deg : Ideal.absNorm 𝔏 = ℓ)
    (δ : (𝓞 Kplus)ˣ)
    (hδeig : ∀ d : (ZMod p)ˣ, ∃ v : (𝓞 Kplus)ˣ,
      Units.mapEquiv (Δact d).toMulEquiv δ = δ ^ ((d : ZMod p) ^ 2).val * v ^ p)
    (hδ𝔏 : (Ideal.Quotient.mk 𝔏 (δ : 𝓞 Kplus))
      ∉ {x : 𝓞 Kplus ⧸ 𝔏 | ∃ y, y ^ p = x}) :
    ∃ (α : Kplus) (_hα : α ≠ 0) (t : ZMod p) (_ht : t ≠ 0) (J : Ideal (𝓞 Kplus)),
      FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 Kplus)) α =
        (∏ d : (ZMod p)ˣ, (𝔏.map (Δact d).toRingHom :
          FractionalIdeal (nonZeroDivisors (𝓞 Kplus)) Kplus) ^
            (t * ((d : ZMod p) ^ 2)⁻¹).val) *
        (J : FractionalIdeal (nonZeroDivisors (𝓞 Kplus)) Kplus) ^ p := by p2m_exact_reverting @_root_.P2MW.S_ExtCitation_Cyclotomic_thaine_relation_plusField.solution
