# 积分和测度论

## 10.1 初等积分

我们首先关注函数在`ℝ`上有限区间的积分。我们可以积分初等函数。

```lean
import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.MeasureTheory.Integral.IntervalIntegral

local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y) -- Porting note: See issue lean4#2220

open MeasureTheory intervalIntegral

open Interval
-- 这里引入了记号`[[a, b]]` 来表示区间`min a b`到`max a b`。

example (a b : ℝ) : (∫ x in a..b, x) = (b ^ 2 - a ^ 2) / 2 :=
  integral_id

example {a b : ℝ} (h : (0 : ℝ) ∉ [[a, b]]) : (∫ x in a..b, 1 / x) = Real.log (b / a) :=
  integral_one_div h
```

微积分基本定理联系了微分和积分。下面我们给出这个定理的两个部分的一种简单情形。
第一部分说明积分是微分的逆运算，第二部分说明了如何计算微元的累积。（这两个部分非常密切相关，但它们的最好版本(没有写在这里)并不等价。）

```lean
example (f : ℝ → ℝ) (hf : Continuous f) (a b : ℝ) : deriv (fun u ↦ ∫ x : ℝ in a..u, f x) b = f b :=
  (integral_hasStrictDerivAt_right (hf.intervalIntegrable _ _) (hf.stronglyMeasurableAtFilter _ _)
        hf.continuousAt).hasDerivAt.deriv

example {f : ℝ → ℝ} {a b : ℝ} {f' : ℝ → ℝ} (h : ∀ x ∈ [[a, b]], HasDerivAt f (f' x) x)
    (h' : IntervalIntegrable f' volume a b) : (∫ y in a..b, f' y) = f b - f a :=
  integral_eq_sub_of_hasDerivAt h h'
```

在Mathlib中也定义了卷积，并证明了卷积的基本性质。

```lean
import Mathlib.Analysis.Convolution

open Convolution

example (f : ℝ → ℝ) (g : ℝ → ℝ) : f ⋆ g = fun x ↦ ∫ t, f t * g (x - t) :=
  rfl
```

## 10.2 测度论

Mathlib中积分的数学基础是测度论。甚至前一节的初等积分实际上也是Bochner积分。Bochner积分是Lebesgue积分的推广，目标空间可以是任意的Banach空间，不一定是有限维的。

测度论的第一部分是集合的$σ$-代数的语言，被称作*可测集*。`MeasurableSpace`类型族提供了带有这种结构的类型。空集`empty`和单元素集`univ`是可测的，可测集的补集是可测的，可数交和可数并是可测的。注意，这些公理是冗余的；如果你`#print MeasurableSpace`，你会看到Mathlib用来构造可测集的公理。可数性条件可以使用`Encodable`类型族来表示。

```lean
import Mathlib.MeasureTheory.MeasurableSpace.Defs

open Set

variable {α : Type*} [MeasurableSpace α]

example : MeasurableSet (∅ : Set α) :=
  MeasurableSet.empty

example : MeasurableSet (univ : Set α) :=
  MeasurableSet.univ

example {s : Set α} (hs : MeasurableSet s) : MeasurableSet (sᶜ) :=
  hs.compl

example : Encodable ℕ := by infer_instance

example (n : ℕ) : Encodable (Fin n) := by infer_instance

variable {ι : Type*} [Encodable ι]

example {f : ι → Set α} (h : ∀ b, MeasurableSet (f b)) : MeasurableSet (⋃ b, f b) :=
  MeasurableSet.iUnion h

example {f : ι → Set α} (h : ∀ b, MeasurableSet (f b)) : MeasurableSet (⋂ b, f b) :=
  MeasurableSet.iInter h
```

如果一个类型是可测的那么我们就可以测量它。字面上，对配备$σ$-代数的集合（或者类型）的测量是一个函数，它是从可测集到扩展（即允许无穷）非负实数的函数，并且满足可数无交并集合上可加性。在Mathlib中，我们不希望每次测量集合时都带着写一个集合可测。因此我们把这个测度推广到任何集合`s`，作为包含`s`的可测集合的测度的最小值。当然，许多引理仍然需要可测假设，但不是全部。

```lean
open MeasureTheory
variable {μ : Measure α}

example (s : Set α) : μ s = ⨅ (t : Set α) (_ : s ⊆ t) (_ : MeasurableSet t), μ t :=
  measure_eq_iInf s

example (s : ι → Set α) : μ (⋃ i, s i) ≤ ∑' i, μ (s i) :=
  measure_iUnion_le s

example {f : ℕ → Set α} (hmeas : ∀ i, MeasurableSet (f i)) (hdis : Pairwise (Disjoint on f)) :
    μ (⋃ i, f i) = ∑' i, μ (f i) :=
  μ.m_iUnion hmeas hdis
```

一旦一个类型有了与它相关联的测度，我们就说，如果性质`P`只在一个测度为0的集合上失效，则`P`“几乎处处”成立(almost everywhere, ae)。几乎处处的性质集合形成了一个过滤器(filter)，但是Mathlib引入了特殊的符号来表示一个性质几乎处处成立。

```lean
example {P : α → Prop} : (∀ᵐ x ∂μ, P x) ↔ ∀ᶠ x in μ.ae, P x :=
  Iff.rfl
```

## 10.3 积分

现在我们有了测度和可测空间，我们就可以考虑积分了。正如前文所讲，Mathlib使用非常一般的积分记号，支持任意的Banach空间。像往常一样，我们不希望我们的记号带有假设，所以我们这样约定：如果函数不可积，那么积分等于零。大多数与积分有关的引理都有可积性假设。

```lean
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
open Set Topology MeasureTheory

section
variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {f : α → E}

example {f g : α → E} (hf : Integrable f μ) (hg : Integrable g μ) :
    ∫ a, f a + g a ∂μ = ∫ a, f a ∂μ + ∫ a, g a ∂μ :=
  integral_add hf hg
```

作为我们做出的各种约定之间复杂交互的一个例子，让我们看看如何积分常值函数。回顾一下测度`μ`是在扩展的非负实数`ℝ≥0∞`上取值的，存在一个函数`ENNReal.toReal : ℝ≥0∞ → ℝ`把无穷点`⊤`映到0。对任意`s : Set α`，如果`μ s = ⊤`，则非零的常值函数在`s`上不可积，因此根据约定积分值为0，刚好是`(μ s).toReal`的结果。所以我们有下面的引理。


```lean
example {s : Set α} (c : E) : ∫ x in s, c ∂μ = (μ s).toReal • c :=
  set_integral_const c
```

现在我们快速地解释如何获得积分理论中最重要的定理，从控制收敛定理开始(dominated convergence theorem)。Mathlib中有几个版本，这里我们只展示最基本的一个。

```lean
open Filter

example {F : ℕ → α → E} {f : α → E} (bound : α → ℝ) (hmeas : ∀ n, AEStronglyMeasurable (F n) μ)
    (hint : Integrable bound μ) (hbound : ∀ n, ∀ᵐ a ∂μ, ‖F n a‖ ≤ bound a)
    (hlim : ∀ᵐ a ∂μ, Tendsto (fun n : ℕ ↦ F n a) atTop (𝓝 (f a))) :
    Tendsto (fun n ↦ ∫ a, F n a ∂μ) atTop (𝓝 (∫ a, f a ∂μ)) :=
  tendsto_integral_of_dominated_convergence bound hmeas hint hbound hlim
```

还有一个积类型上的积分的Fubini定理：

```lean
example {α : Type*} [MeasurableSpace α] {μ : Measure α} [SigmaFinite μ] {β : Type*}
    [MeasurableSpace β] {ν : Measure β} [SigmaFinite ν] (f : α × β → E)
    (hf : Integrable f (μ.prod ν)) : ∫ z, f z ∂ μ.prod ν = ∫ x, ∫ y, f (x, y) ∂ν ∂μ :=
  integral_prod f hf
```

有一个非常一般的版本的卷积适用于任何连续双线性形式。

```lean
import Mathlib.Analysis.Convolution
open Convolution

variable {𝕜 : Type*} {G : Type*} {E : Type*} {E' : Type*} {F : Type*} [NormedAddCommGroup E]
  [NormedAddCommGroup E'] [NormedAddCommGroup F] [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 E]
  [NormedSpace 𝕜 E'] [NormedSpace 𝕜 F] [MeasurableSpace G] [NormedSpace ℝ F] [CompleteSpace F]
  [Sub G]

example (f : G → E) (g : G → E') (L : E →L[𝕜] E' →L[𝕜] F) (μ : Measure G) :
    f ⋆[L, μ] g = fun x ↦ ∫ t, L (f t) (g (x - t)) ∂μ :=
  rfl
```

最后，Mathlib有一个非常一般的换元公式。下面的命题中，`BorelSpace E`意为由开集`E`生成的`E`上的$σ$-代数，`IsAddHaarMeasure μ`意为测度`μ`是左不变的(left-invariant)，在紧集上有限，在开集上为正数。

```lean
import Mathlib.MeasureTheory.Function.Jacobian

example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] {s : Set E} {f : E → E}
    {f' : E → E →L[ℝ] E} (hs : MeasurableSet s)
    (hf : ∀ x : E, x ∈ s → HasFDerivWithinAt f (f' x) s x) (h_inj : InjOn f s) (g : E → F) :
    ∫ x in f '' s, g x ∂μ = ∫ x in s, |(f' x).det| • g (f x) ∂μ :=
  integral_image_eq_integral_abs_det_fderiv_smul μ hs hf h_inj g
```