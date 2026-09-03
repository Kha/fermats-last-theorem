import Mathlib
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_Correspondence
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_RegularProlongation_exists_norm_mem_integers_and_residue_norm_eq_norm_residue

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.RegularProlongation.exists_norm_mem_integers_and_residue_norm_eq_norm_residue
    {L F F' k k' : Type*} [Field L] [Field F] [Field F'] [Field k] [Field k']
    [Algebra L F] [Algebra L F']
    (A : ValuationSubring L) [Algebra (IsLocalRing.ResidueField ↥A) k] [Algebra (IsLocalRing.ResidueField ↥A) k']
    (R : AlgebraicCurve.RegularProlongation A F k) (R' : AlgebraicCurve.RegularProlongation A F' k')
    (φ : F →ₐ[L] F') (ι : k →+* k')

    (hint : ∀ f : F, φ f ∈ R'.integers ↔ f ∈ R.integers)
    (hres : ∀ (f : F) (hf : f ∈ R.integers) (hf' : φ f ∈ R'.integers), R'.residue ⟨φ f, hf'⟩ = ι (R.residue ⟨f, hf⟩))

    (n : ℕ) (hn : AlgebraicCurve.finrankAlong L φ = n)
    (b : Fin n → F') (hb : ∀ i, b i ∈ R'.integers)
    (hli : letI := ι.toAlgebra; LinearIndependent k (fun i => R'.residue ⟨b i, hb i⟩))
    (hsp : letI := ι.toAlgebra; Submodule.span k (Set.range (fun i => R'.residue ⟨b i, hb i⟩)) = ⊤)
    (h : F') (hh : h ∈ R'.integers) :
    ∃ hN : (letI := AlgebraicCurve.algebraAlong φ; Algebra.norm F h) ∈ R.integers,
      R.residue ⟨_, hN⟩ = (letI := ι.toAlgebra; Algebra.norm k (R'.residue ⟨h, hh⟩)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_RegularProlongation_exists_norm_mem_integers_and_residue_norm_eq_norm_residue.solution
