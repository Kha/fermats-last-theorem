import Mathlib
import Definitions.Def_NumberField_LevelArithmeticModP
import Definitions.Def_NumberField_SIdeleModule
import P2M.Util
import P2M.Sol.S_NumberField_LevelArith_exists_coboundary_localUnits_infinitePlace_of_forall_conj_archimedeanDecomposition

set_option autoImplicit false

open CategoryTheory IsDedekindDomain NumberField NumberField.LevelArith ExtCitation
open scoped NumberField.LevelArith NumberField.InfPlaceDecomp

theorem NumberField.LevelArith.exists_coboundary_localUnits_infinitePlace_of_forall_conj_archimedeanDecomposition
    (L F : IntermediateField ℚ (AlgebraicClosure ℚ)) (hLF : L ≤ F)
    [FiniteDimensional ℚ ↥L] [FiniteDimensional ℚ ↥F] [Normal ℚ ↥F] [Normal ↥L ↥(levelField L F hLF)]
    (T : Finset (HeightOneSpectrum (𝓞 ↥L)))
    (f : groupCohomology.cocycles₂ (NumberField.SUnits.sUnitsRep ↥L ↥(levelField L F hLF) T))
    (v : InfinitePlace ↥L)
    (hyp : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      (hσ : ∀ g : ↥archimedeanDecomposition,
        σ * (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) * σ⁻¹ ∈ L.fixingSubgroup),
      ∃ c₁ : ↥archimedeanDecomposition → Additive (AlgebraicClosure ℚ)ˣ, ∀ g h : ↥archimedeanDecomposition,
        Additive.ofMul (Units.map (algebraMap ↥(levelField L F hLF) (AlgebraicClosure ℚ)).toMonoidHom
            (NumberField.SUnits.val ↥L ↥(levelField L F hLF) T
              (f (levelGal L F hLF ⟨σ * (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) * σ⁻¹, hσ g⟩,
                  levelGal L F hLF ⟨σ * (h : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) * σ⁻¹, hσ h⟩)))) =
          Additive.ofMul ((σ * (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) * σ⁻¹) • Additive.toMul (c₁ h))
            - c₁ (g * h) + c₁ g) :
    ∃ y : ↥(NumberField.InfPlaceDecomp.decomp ↥L ↥(levelField L F hLF)
          (NumberField.ArchIdele.above ↥L ↥(levelField L F hLF) v)) →
        NumberField.InfPlaceDecomp.localUnits ↥L ↥(levelField L F hLF) (NumberField.ArchIdele.above ↥L ↥(levelField L F hLF) v),
      ∀ a b : ↥(NumberField.InfPlaceDecomp.decomp ↥L ↥(levelField L F hLF) (NumberField.ArchIdele.above ↥L ↥(levelField L F hLF) v)),
        Additive.ofMul (Units.map (NumberField.SIdele.locInf ↥L ↥(levelField L F hLF) v).toMonoidHom
            (NumberField.SUnits.val ↥L ↥(levelField L F hLF) T
              (f ((a : ↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)),
                  (b : ↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)))))) =
          (NumberField.InfPlaceDecomp.localUnits ↥L ↥(levelField L F hLF)
              (NumberField.ArchIdele.above ↥L ↥(levelField L F hLF) v)).ρ a (y b) - y (a * b) + y a := by p2m_exact_reverting @_root_.P2MW.S_NumberField_LevelArith_exists_coboundary_localUnits_infinitePlace_of_forall_conj_archimedeanDecomposition.solution
