import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Definitions.Def_AlgebraicCurve_RegularProlongation
import P2M.Util
import P2M.Sol.S_ModularCurve_JHPlaceSpecialization_ProlongationDatum_residue_snd_eq_zero_of_residue_fst_hasValue_zero_of_nodeValueLaw

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.JHNeronObjectAtP
open scoped MatrixGroups

theorem ModularCurve.JHPlaceSpecialization.ProlongationDatum.residue_snd_eq_zero_of_residue_fst_hasValue_zero_of_nodeValueLaw
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) [NeZero (M / p)]
    (A : ValuationSubring (AlgebraicClosure ℚ))
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (α β : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα : α.IsIntegral) (hβ : β.IsIntegral)
    (δ : Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) → Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)))
    (SS : Finset (Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))))
    (Psp : JHPlaceSpecialization p M H hpM A) (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ)
    (hnv : Rpd.NodeValueLaw α β hα hβ δ SS)
    (u : ↥(xHFunctionFieldBar M H)) (h₁ : u ∈ Rpd.R₁.integers) (hres₁ : Rpd.R₁.residue ⟨u, h₁⟩ ≠ 0)
    (s : Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))) (hs : s ∈ SS)

    (hnodiv : ∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), V.ord u ≠ 0 → ¬ (Psp.reduceFst α hα V = s.1 ∧ Psp.reduceSnd β hβ δ V = s.2))
    (hvan : s.1.HasValue (Rpd.R₁.residue ⟨u, h₁⟩ : Fbar p M H hpM (ResidueField ↥A)) 0) :
    ∀ h₂ : u ∈ Rpd.R₂.integers, Rpd.R₂.residue ⟨u, h₂⟩ = 0 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_JHPlaceSpecialization_ProlongationDatum_residue_snd_eq_zero_of_residue_fst_hasValue_zero_of_nodeValueLaw.solution
