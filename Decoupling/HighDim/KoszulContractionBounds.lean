import Decoupling.HighDim.KoszulContractionMap

/-!
# Bounded finite-free tensor models

The finiteness, freeness, and both cochain bounds used for tensoring the
explicit contraction are consequences of the actual cell modules.
-/
namespace Decoupling.HighDim.KoszulContraction
open CategoryTheory CategoryTheory.Limits Koszul TrivialLayers ExtValuesTensor
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {K : Type} [Field K] {D : ℕ}
  (B : ModuleCat (Laurent K D)) [FiniteDimensional K (Layers.coefficients B)]

instance tensorTerm_finite (n : ℕ) : Module.Finite (Laurent K D) (TensorTerm B n) :=
  Module.Finite.equiv (tensorTermEquiv B n).symm

instance tensorTerm_free (n : ℕ) : Module.Free (Laurent K D) (TensorTerm B n) :=
  Module.Free.of_equiv (tensorTermEquiv B n).symm

variable (hB : AugmentationAction B)

instance complex_term_finite (p : ℤ) : Module.Finite (Laurent K D) ((complex B hB).X p) := by
  by_cases hp : p ≤ 0
  · obtain ⟨n, rfl⟩ := Int.exists_eq_neg_ofNat hp
    let : Module.Finite (Laurent K D) ((resolution B hB).complex.X n) := by
      change Module.Finite (Laurent K D) (TensorTerm B n)
      infer_instance
    exact Module.Finite.equiv ((resolution B hB).cochainComplexXIso (-n) n).symm.toLinearEquiv
  · let : Subsingleton ((complex B hB).X p) := ModuleCat.subsingleton_of_isZero
      ((complex B hB).isZero_of_isStrictlyLE 0 p (by omega))
    infer_instance

instance complex_term_free (p : ℤ) : Module.Free (Laurent K D) ((complex B hB).X p) := by
  by_cases hp : p ≤ 0
  · obtain ⟨n, rfl⟩ := Int.exists_eq_neg_ofNat hp
    let : Module.Free (Laurent K D) ((resolution B hB).complex.X n) := by
      change Module.Free (Laurent K D) (TensorTerm B n)
      infer_instance
    exact Module.Free.of_equiv ((resolution B hB).cochainComplexXIso (-n) n).symm.toLinearEquiv
  · let : Subsingleton ((complex B hB).X p) := ModuleCat.subsingleton_of_isZero
      ((complex B hB).isZero_of_isStrictlyLE 0 p (by omega))
    infer_instance

instance complex_boundedBelow : (complex B hB).IsStrictlyGE (-(D : ℤ)) := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro p hp
  obtain ⟨n, rfl⟩ := Int.exists_eq_neg_ofNat (by omega : p ≤ 0)
  have hn : D < n := by omega
  let : Subsingleton (Term (Laurent K D) D n) := term_subsingleton (Laurent K D) hn
  let : Subsingleton (TensorTerm B n) := inferInstance
  let : Subsingleton ((tensorComplex B).X n) := ‹Subsingleton (TensorTerm B n)›
  exact (ModuleCat.isZero_of_subsingleton ((tensorComplex B).X n)).of_iso
    ((resolution B hB).cochainComplexXIso (-n) n)

end
end Decoupling.HighDim.KoszulContraction
