import Decoupling.HighDim.ScalingSplitting

/-!
# Lemma 2: one actual p-coarse-graining step

Source: `drafts/main.tex`, Lemma `lem:one-step`. The lower part is already
split, as required by the lemma. Positive Ext vanishing is proved internally
by Lemma 1; it is not an extra hypothesis. The triangle is the canonical
Postnikov triangle of the actual derived object, and augmentation triviality
and finite coefficient dimension persist after this restriction.
-/

namespace Decoupling.HighDim.OneStep

open CategoryTheory CategoryTheory.Limits
open ScalingSplitting PostnikovTruncation
noncomputable section
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false

variable {K : Type} [Field K] {D : ℕ} (p : ℕ) [Fact p.Prime] [CharP K p]

/-- The canonical triangle splits after one p-restriction, with its actual
inclusion and projection preserved. Apply this to τ≤j of the profile. -/
theorem splits (X : DerivedCategory (ModuleCat.{0} (Laurent K D))) (j : ℤ) [X.IsLE j]
    {ι : Type} [Fintype ι] (degree : ι → ℤ) (B : ι → ModuleCat.{0} (Laurent K D))
    (hdeg : ∀ i, degree i < j)
    (eLower : lower X j ≅ ⨁ (fun i =>
      (DerivedCategory.singleFunctor (ModuleCat (Laurent K D)) (degree i)).obj (B i)))
    (hB : ∀ i, TrivialFinite (B i)) (hTop : TrivialFinite (PostnikovInduction.H X j)) :
    ∃ e : (restriction p).mapDerivedCategory.obj (lower X j) ⊞
        (restriction p).mapDerivedCategory.obj (upper X j) ≅
          (restriction p).mapDerivedCategory.obj X,
      biprod.inl ≫ e.hom = (restriction p).mapDerivedCategory.map (triangle X j).mor₁ ∧
        e.hom ≫ (restriction p).mapDerivedCategory.map (triangle X j).mor₂ = biprod.snd := by
  apply PostnikovExtStep.splits_of_native_ext (restriction p) (triangle X j)
    (t.triangleLTGE_distinguished j X) degree B j (PostnikovInduction.H X j)
    hdeg eLower (upperSingleIso X j)
  intro i n hn a
  have : FiniteDimensional K (Layers.coefficients (PostnikovInduction.H X j)) := hTop.2
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  exact ExtRestrictionVanishing.of_augmentationAction p _ _ hTop.1 (hB i).1 n a

omit [Fact p.Prime] [CharP K p] in
/-- After renaming the retained variables, the same actual layer is still
annihilated by the augmentation ideal and has finite coefficient dimension. -/
theorem layers_remain_trivial (M : ModuleCat.{0} (Laurent K D)) (h : TrivialFinite M) :
    TrivialFinite ((restriction p).obj M) := trivialFinite_restriction p M h

end
end Decoupling.HighDim.OneStep
