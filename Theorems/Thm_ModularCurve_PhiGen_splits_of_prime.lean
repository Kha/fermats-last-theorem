module

public import Definitions.Def_ModularCurve_X0
public import Definitions.Def_ModularCurve_PhiGen
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import P2M.Util
import P2M.Sol.S_ModularCurve_PhiGen_splits_of_prime

@[expose] public section

open ModularCurve ModularCurve.PhiGen
theorem ModularCurve.PhiGen.splits_of_prime {K : Type*} [Field K] [Algebra ℚ K] (p : ℕ) [hp : Fact (Nat.Prime p)] (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) p) (data : ModularPolynomialData p) : data.Φ.map (((coeffEmb K).comp (qExpand ℚ p)).comp evalAtJ) = phiProd p (conj p ζ) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_PhiGen_splits_of_prime.solution
