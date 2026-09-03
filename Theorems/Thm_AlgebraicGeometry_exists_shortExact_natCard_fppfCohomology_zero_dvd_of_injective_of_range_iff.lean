import Definitions.Def_AlgebraicGeometry_FppfKummerProp17
import Definitions.Def_AlgebraicGeometry_FppfH0Identification
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_exists_shortExact_natCard_fppfCohomology_zero_dvd_of_injective_of_range_iff
open AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory

theorem AlgebraicGeometry.exists_shortExact_natCard_fppfCohomology_zero_dvd_of_injective_of_range_iff
    (p : ℕ) [Fact p.Prime] (q : ℕ)
    (L : Sheaf (smallFppfTopology specInt) Ab.{1})
    (C : Sheaf (smallFppfTopology specInt) Ab.{1})
    (iC : C.obj ≅ (Scheme.Fppf.forget specInt ⋙ Over.forget specInt).op ⋙
      (FppfKummerSES.muPAbelianSheafLifted.{0} q).obj)
    (f : L ⟶ C) (hinj : ∀ U : specInt.Fppf, Function.Injective (f.hom.app (Opposite.op U)))
    (hrange :
      ∀ (U : specInt.Fppf) (s : C.obj.obj (Opposite.op U)),
        s ∈ Set.range (f.hom.app (Opposite.op U)) ↔
          ∃ a : Γ(U.left, ⊤), a - 1 ∈ Ideal.span {(p : Γ(U.left, ⊤))} ∧
            a * ((FppfKummerSES.gmLiftedSectionUnit
                    ((Limits.kernel.ι (FppfKummerSES.gmPowSelf.{0} q)).hom.app (Opposite.op U.left)
                      (iC.hom.app (Opposite.op U) s)) : Γ(U.left, ⊤)) - 1) = 0) :
    ∃ (Q : Sheaf (smallFppfTopology specInt) Ab.{1}) (g : C ⟶ Q) (w : f ≫ g = 0),
      (ShortComplex.mk f g w).ShortExact ∧ Nat.card (fppfCohomology specInt Q 0) ∣ q := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_shortExact_natCard_fppfCohomology_zero_dvd_of_injective_of_range_iff.solution
