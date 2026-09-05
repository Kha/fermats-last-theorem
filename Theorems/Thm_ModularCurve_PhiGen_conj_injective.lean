module

public import Definitions.Def_ModularCurve_X0
public import Definitions.Def_ModularCurve_PhiGen
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import P2M.Util
import P2M.Sol.S_ModularCurve_PhiGen_conj_injective

@[expose] public section

open ModularCurve ModularCurve.PhiGen
theorem ModularCurve.PhiGen.conj_injective {K : Type*} [Field K] [Algebra ℚ K] (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)] (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) ℓ) : Function.Injective (conj ℓ ζ (K := K)) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_PhiGen_conj_injective.solution
