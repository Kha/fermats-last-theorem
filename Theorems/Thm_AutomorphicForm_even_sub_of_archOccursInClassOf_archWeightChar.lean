import Definitions.Def_AutomorphicForm_TranslateSpanOccurrence
import Definitions.Def_AutomorphicForm_ArchLoweringAnnihilated
import P2M.Util
import P2M.Sol.S_AutomorphicForm_even_sub_of_archOccursInClassOf_archWeightChar

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox AutomorphicForm AutomorphicForm.WindowedSiegel
  AutomorphicForm.SiegelCovering NumberField.InfinitePlace NumberField.InfinitePlace.Completion

theorem AutomorphicForm.even_sub_of_archOccursInClassOf_archWeightChar
    (F : Type) [Field F] [NumberField F] (D : Set (AdelicGL2 (𝓞 F) F)) (Θ : HeckeEigensystem F ℂ)
    (w : InfinitePlace F) (hw : w.IsReal) (n m : ℤ)
    (hn : ArchOccursInClassOf F D Θ
      (fun φ => HasArchCharacterAt₀ F w
        ((archWeightCharℝ n).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw)
          (norm_ringEquivRealOfIsReal hw))) φ))
    (hm : ArchOccursInClassOf F D Θ
      (fun φ => HasArchCharacterAt₀ F w
        ((archWeightCharℝ m).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw)
          (norm_ringEquivRealOfIsReal hw))) φ)) :
    Even (n - m) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_even_sub_of_archOccursInClassOf_archWeightChar.solution
