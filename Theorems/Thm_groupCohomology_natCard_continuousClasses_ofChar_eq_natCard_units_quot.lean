import Mathlib
import Definitions.Def_DualSelmer_ExtConditions
import P2M.Util
import P2M.Sol.S_groupCohomology_natCard_continuousClasses_ofChar_eq_natCard_units_quot
attribute [-instance] groupCohomology.Kummer.instMulDistribMulActionRootsOfUnity
attribute [-simp] groupCohomology.Kummer.coe_kummerCocycleRoots groupCohomology.Kummer.mem_powerSubgroup_iff groupCohomology.Kummer.val_smul_units groupCohomology.Kummer.kummerHom_apply groupCohomology.Kummer.coe_smul_rootsOfUnity

set_option autoImplicit false
universe u
open CategoryTheory groupCohomology
theorem groupCohomology.natCard_continuousClasses_ofChar_eq_natCard_units_quot
    {K L : Type} [Field K] [Field L] [Algebra K L] [IsGalois K L] {p : ℕ} [Fact p.Prime]
    (χ : (L ≃ₐ[K] L) →* (ZMod p)ˣ) {ζ : Lˣ} (hζp : IsPrimitiveRoot ζ p)
    (hζ : ∀ g : L ≃ₐ[K] L, g • ζ = ζ ^ (χ g : ZMod p).val)
    (hroots : ∀ a : Kˣ, ∃ α : Lˣ, algebraMap K L (a : K) = (α : L) ^ p)
    (adm : Submodule (ZMod p) (H1 (ofChar χ)))
    (hadm : ∀ x, x ∈ adm ↔ ∃ c : cocycles₁ (ofChar χ),
      (∃ E : IntermediateField K L, FiniteDimensional K E ∧
        ∀ g s : L ≃ₐ[K] L, s ∈ E.fixingSubgroup → c.val (g * s) = c.val g) ∧ (H1π _).hom c = x) :
    Nat.card adm = Nat.card (Kˣ ⧸ (powMonoidHom p : Kˣ →* Kˣ).range) := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_natCard_continuousClasses_ofChar_eq_natCard_units_quot.solution
