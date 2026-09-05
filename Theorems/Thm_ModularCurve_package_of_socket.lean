module

public import Definitions.Def_ModularCurve_PhiGen
public import Definitions.Def_ModularCurve_JqCoeff
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import P2M.Util
import P2M.Sol.S_ModularCurve_package_of_socket

@[expose] public section

open ModularCurve ModularCurve.PhiGen
theorem ModularCurve.package_of_socket {K : Type*} [Field K] (M : ℕ) [NeZero M] (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) M)
    (hbase : ∀ (p : ℕ) [Fact (Nat.Prime p)], p ∣ M →
      jqNModC K p ∉ IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K))) :
    ∀ d : ℕ, d ∣ M → ∀ [NeZero d],
      Module.finrank (IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K)))
          (IntermediateField.adjoin (IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K)))
            ({jqNModC K d} : Set (LaurentSeries K))) = dedekindPsi d
        ∧ modularFunctionFieldC K d = IntermediateField.adjoin K
            {x : LaurentSeries K | ∃ (d' : ℕ) (_ : NeZero d'), d' ∣ d ∧ x = jqNModC K d'} := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_package_of_socket.solution
