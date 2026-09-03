import Definitions.Def_CerednikDrinfeld_MumfordPeriod
import Definitions.Def_CerednikDrinfeld_ToricUniformization
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_Mumford_PeriodDatum_kummer_of_ord_Q

set_option autoImplicit false

open ModularCurve CerednikDrinfeld CerednikDrinfeld.Mumford

theorem CerednikDrinfeld.Mumford.PeriodDatum.kummer_of_ord_Q
    {E V : Type} [Fintype E] [Fintype V] [DecidableEq V] {D : DegeneracyData E V}
    {K L : Type} [Field K] [Field L] [Algebra K L] {ord : Additive Kˣ →+ ℤ}
    (P : PeriodDatum D K L ord) {p : ℕ} [Fact p.Prime] {ζ : Lˣ} (hζ : IsPrimitiveRoot ζ p)
    (χ : ↥(Submodule.torsionBy ℤ ↥P.U (p : ℤ)) → (↥(ribbonKernel D) →ₗ[ℤ] ZMod p))
    (hχ : ∀ (v : ↥(Submodule.torsionBy ℤ ↥P.U (p : ℤ))) (z : ↥(ribbonKernel D)),
      Additive.toMul (((v : ↥P.U) : P.TorusPoints) z) = ζ ^ (χ v z).val)
    (s : L →+* L) (hsK : ∀ k : K, s (algebraMap K L k) = algebraMap K L k) (hsζ : s ζ = ζ)
    (ϖ : Kˣ) (hϖ : ord (Additive.ofMul ϖ) = 1)
    (hensel : ∀ a : Kˣ, ord (Additive.ofMul a) = 0 → ∃ c : Kˣ, c ^ p = a)
    (τ : ZMod p) (hτ : ∀ b : L, b ^ p = algebraMap K L ϖ → s b = (ζ : L) ^ τ.val * b)
    (u : ↥P.U) (x : ↥(ribbonKernel D)) (hu : (p : ℤ) • (u : P.TorusPoints) = P.QL x) :
    ∃ v : ↥(Submodule.torsionBy ℤ ↥P.U (p : ℤ)),
      (∀ z : ↥(ribbonKernel D),
        Additive.ofMul (Units.map (s : L →* L) (Additive.toMul ((u : P.TorusPoints) z))) =
          (u : P.TorusPoints) z + ((v : ↥P.U) : P.TorusPoints) z) ∧
      χ v = τ • ribbonGramModP p D x := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_Mumford_PeriodDatum_kummer_of_ord_Q.solution
