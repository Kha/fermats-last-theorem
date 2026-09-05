module

public import Definitions.Def_ModularCurve_X0
public import Definitions.Def_ModularCurve_LaurentCoeff
public import Definitions.Def_ModularCurve_PhiGen
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import P2M.Util
import P2M.Sol.S_ModularCurve_PhiGen_splits_prime_at_slot

@[expose] public section

open ModularCurve ModularCurve.PhiGen
theorem ModularCurve.PhiGen.splits_prime_at_slot {K : Type*} [Field K] [Algebra ℚ K] (N : ℕ) [NeZero N] (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) N) (p : ℕ) [hp : Fact (Nat.Prime p)] (hpN : p ∣ N) (data : ModularPolynomialData p) (e : ℕ) [NeZero e] (u : Kˣ) : data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries K)) (qExpand K (p * e) (qTwist (u ^ p) (coeffEmb K jq)))) = (Polynomial.X - Polynomial.C (qExpand K (p * (p * e)) (qTwist (u ^ (p * p)) (coeffEmb K jq)))) * ∏ b ∈ Finset.range p, (Polynomial.X - Polynomial.C (qExpand K e (qTwist (u * ζ ^ (b * (N / p))) (coeffEmb K jq)))) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_PhiGen_splits_prime_at_slot.solution
