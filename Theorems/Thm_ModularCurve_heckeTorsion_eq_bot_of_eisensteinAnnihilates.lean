import Definitions.Def_ModularCurve_AtPPackage
import P2M.Util
import P2M.Sol.S_ModularCurve_heckeTorsion_eq_bot_of_eisensteinAnnihilates

namespace ModularCurve
theorem heckeTorsion_eq_bot_of_eisensteinAnnihilates
    {S : Finset Nat.Primes} {Φ : Type*} [AddCommGroup Φ] [Module HeckeAlg Φ]
    (hΦ : EisensteinAnnihilates S Φ)
    {𝔪 : Ideal HeckeAlg} (hmax : 𝔪.IsMaximal) {ℓ : Nat.Primes} (hℓ : ℓ ∉ S)
    (hne : heckeGen ℓ - MvPolynomial.C (((ℓ : ℕ) : ℤ) + 1) ∉ 𝔪) :
    heckeTorsion Φ 𝔪 = ⊥ := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_heckeTorsion_eq_bot_of_eisensteinAnnihilates.solution
end ModularCurve
