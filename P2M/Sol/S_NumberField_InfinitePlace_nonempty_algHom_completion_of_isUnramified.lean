import Definitions.Def_AutomorphicForm_TwistedOrbital
import Mathlib.NumberTheory.NumberField.Completion.Ramification
import P2M.Util
namespace P2MW.S_NumberField_InfinitePlace_nonempty_algHom_completion_of_isUnramified

set_option autoImplicit false

open NumberField
open scoped NumberField.LiesOver

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : InfinitePlace K) (w : InfinitePlace L) (hw : w.comap (algebraMap K L) = v)
    (hun : w.IsUnramified K) :
    Nonempty (L →ₐ[K] v.Completion) := by
  haveI : w.1.LiesOver v.1 := ⟨congrArg Subtype.val hw⟩
  let e : v.Completion →ₐ[K] w.Completion := IsScalarTower.toAlgHom K v.Completion w.Completion
  have hfin : Module.finrank v.Completion w.Completion = 1 :=
    InfinitePlace.Completion.finrank_eq_one_of_isUnramified v hun
  have hsurj : Function.Surjective e := by
    intro y
    have hy : (y : w.Completion) ∈ (⊥ : Subalgebra v.Completion w.Completion) := by
      rw [Subalgebra.bot_eq_top_of_finrank_eq_one hfin]
      exact Algebra.mem_top
    obtain ⟨x, hx⟩ := Algebra.mem_bot.mp hy
    exact ⟨x, hx⟩
  have hinj : Function.Injective e := (algebraMap v.Completion w.Completion).injective
  exact ⟨((AlgEquiv.ofBijective e ⟨hinj, hsurj⟩).symm : w.Completion →ₐ[K] v.Completion).comp
    (IsScalarTower.toAlgHom K L w.Completion)⟩
