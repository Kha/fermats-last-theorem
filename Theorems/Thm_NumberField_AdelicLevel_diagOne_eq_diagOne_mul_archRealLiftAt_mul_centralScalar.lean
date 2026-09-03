import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Definitions.Def_NumberField_AdelicTraceFin
import P2M.Util
import P2M.Sol.S_NumberField_AdelicLevel_diagOne_eq_diagOne_mul_archRealLiftAt_mul_centralScalar

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm IsDedekindDomain

theorem NumberField.AdelicLevel.diagOne_eq_diagOne_mul_archRealLiftAt_mul_centralScalar
    (K : Type) [Field K] [NumberField K]
    (w : InfinitePlace K) (hw : w.IsReal) (ε : ℝ) (hε : ε = 1 ∨ ε = -1) (u : ℝ) (hu : 0 < u)
    (a b' z : (AdeleRing (𝓞 K) K)ˣ)
    (ha : ((a : (AdeleRing (𝓞 K) K))).2 = 1) (hb' : ((b' : (AdeleRing (𝓞 K) K))).2 = 1) (hz : ((z : (AdeleRing (𝓞 K) K))).2 = 1)
    (hab : ∀ w' : InfinitePlace K, w' ≠ w → ((a : (AdeleRing (𝓞 K) K))).1 w' = ((b' : (AdeleRing (𝓞 K) K))).1 w')
    (hbw : ((b' : (AdeleRing (𝓞 K) K))).1 w = 1)
    (haw : InfinitePlace.Completion.ringEquivRealOfIsReal hw (((a : (AdeleRing (𝓞 K) K))).1 w) = ε * u)
    (hzw' : ∀ w' : InfinitePlace K, w' ≠ w → ((z : (AdeleRing (𝓞 K) K))).1 w' = 1)
    (hzw : InfinitePlace.Completion.ringEquivRealOfIsReal hw (((z : (AdeleRing (𝓞 K) K))).1 w) = Real.sqrt u) :
    diagOne a = diagOne b' * archRealLiftAt hw (Matrix.of.symm !![ε * Real.sqrt u, 0; 0, (Real.sqrt u)⁻¹]) *
        centralScalar (𝓞 K) K z ∧
      archComponent K w (glArch (𝓞 K) K (diagOne b')) = 1 := by p2m_exact_reverting @_root_.P2MW.S_NumberField_AdelicLevel_diagOne_eq_diagOne_mul_archRealLiftAt_mul_centralScalar.solution
