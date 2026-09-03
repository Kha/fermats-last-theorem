import Definitions.Def_ModularCurve_FullLevelSemistableCoveringNaturality
import Definitions.Def_ModularCurve_FullLevelSemistableCoveringGuards
import Definitions.Def_ModularCurve_FullLevelSemistableCoveringW2
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_ResidueDiscs
import Definitions.Def_ModularCurve_PlaceWidthChar
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_GaloisRep_TameCharacter
import Definitions.Def_ModularCurve_ArithmeticGalois
import P2M.Util
import P2M.Sol.S_ModularCurve_FullLevel_SemistableCovering_exists_drinfeldClause_of_regularProlongation_of_exists_algEquiv_quotField_hedged

set_option autoImplicit false

open AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

theorem ModularCurve.FullLevel.SemistableCovering.exists_drinfeldClause_of_regularProlongation_of_exists_algEquiv_quotField_hedged
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M']
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')))
    (𝒞 : SemistableCovering q M' A W) (s : ↥W)
    (π : AlgebraicClosure ℚ)
    {FSS : Type} [Field FSS] [Algebra (ResidueField A) FSS]
    (R : RegularProlongation A (fieldBar q M') FSS)
    (hR : R.integers = (𝒞.CSS s).integers)
    (hfix : ∀ (ζ : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' →
      R.integers.comap (levelAutBar q M' ζ γ).toAlgHom.toRingHom = R.integers)
    {nCs : ℕ}
    (hDL : (∀ (ι : GaloisField q 2 →+* ResidueField ↥A),
            letI : Algebra (GaloisField q 2) (ResidueField ↥A) := ι.toAlgebra
            ∀ (_ : IsDomain (DrinfeldCurve.CoordRing q (ResidueField ↥A))),
            ∃ (Cs : Subgroup (rootsOfUnity (q + 1) (GaloisField q 2))),
              Nat.card Cs = nCs ∧
              ∀ (ζ : Idx q), ∃ η : ℕ, (η = 1 ∨ η = q) ∧ ∃ (e : FSS ≃ₐ[ResidueField ↥A] ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs)),
                (∀ (γ : SL(2, ℤ)), γ ∈ Gamma0 M' →
                  ∀ (hτ : ∀ f : ↥(fieldBar q M'), levelAutBar q M' ζ γ⁻¹ f ∈ R.integers ↔ f ∈ R.integers)
                    (hmem : (redQ q γ, (1 : (GaloisField q 2)ˣ)) ∈ DrinfeldCurve.hSubgroup q),
                    ∀ x : FSS,
                      ((e (R.resAut (levelAutBar q M' ζ γ⁻¹) hτ x) : ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs)) : DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A)) =
                        DrinfeldCurve.hFunctionFieldAction q (ResidueField ↥A) ⟨_, hmem⟩ ((e x : ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs)) : DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A))) ∧
                (∀ τ ∈ A.inertiaSubgroupIn ℚ, ∀ α : (GaloisField q 2)ˣ,
                  ι (α : GaloisField q 2) = A.tameCharacter π τ →
                  ∀ (g : SemilinearAut (AlgebraicClosure ℚ) ↥(fieldBar q M')),
                    g = ModularCurve.arithmeticGalois (xHFunctionField (q ^ 2 * M') (levelH q M')) τ →
                  (∀ f : ↥(fieldBar q M'), g • f ∈ R.integers ↔ f ∈ R.integers) ∧
                  ∀ (hst : ∀ f : ↥(fieldBar q M'), g • f ∈ R.integers ↔ f ∈ R.integers)
                    (φ : FSS ≃+* FSS),
                    (∀ (f : ↥(fieldBar q M')) (hf : f ∈ R.integers),
                      R.residue ⟨g • f, (hst f).mpr hf⟩ = φ (R.residue ⟨f, hf⟩)) →
                    ∀ (d : (ZMod q)ˣ), algebraMap (ZMod q) (GaloisField q 2) (d : ZMod q) = (α : GaloisField q 2) ^ (q + 1) →
                      ∀ (hmem : (diagOneElem q (d ^ η)⁻¹, α ^ η) ∈ DrinfeldCurve.hSubgroup q),
                        ∀ x : FSS,
                          ((e (φ x) : ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs)) : DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A)) =
                            DrinfeldCurve.hFunctionFieldAction q (ResidueField ↥A) ⟨_, hmem⟩ ((e x : ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs)) : DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A)))))
    (ι : GaloisField q 2 →+* ResidueField A)
    [IsDomain (DrinfeldCurve.CoordRing q (ResidueField A))] :
    letI : Algebra (GaloisField q 2) (ResidueField A) := ι.toAlgebra
    ∀ ζ : Idx q, ∃ η : ℕ, (η = 1 ∨ η = q) ∧ 𝒞.DrinfeldClause π ι η ζ s := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_FullLevel_SemistableCovering_exists_drinfeldClause_of_regularProlongation_of_exists_algEquiv_quotField_hedged.solution
