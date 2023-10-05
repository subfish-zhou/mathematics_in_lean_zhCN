# 2 基础部分

本章会介绍Lean中数学推理的具体细节: 计算, 使用引理和定理, 以及对一般结构的推理.

## 2.1 计算

我们一般不把计算看成证明, 但是我们在验证每一个计算步骤的时候---正如lean要求我们做的那样, 说明左边等于右边的行为就是一个证明.

在Lean中, 陈述一个定理等价于确立一个证明该定理的目标. Lean提供`rewrite`策略, 缩写为`rw`, 用于在目标中实现等式代换, 把目标中出现在等式左边的项代换成右边的项. 如果`a`, `b`, `c`是实数, `mul_assoc a b c`是乘法结合律等式`a * b * c = a * (b * c)`, `mul_comm a b`是乘法交换律等式`a * b = b * a`. 在Lean中, 乘法是左结合的, 因此`mul_assoc`的左边也可以写为`（a * b）* c`. 然而通常情况下, 注意Lean的符号约定并在Lean也这样做时省略括号是很好的写作习惯. 

让我们试一下`rw`:

```lean
import Mathlib.Data.Real.Basic
example (a b c : ℝ) : a * b * c = b * (a * c) := by
  rw [mul_comm a b]
  rw [mul_assoc b a c]
```

开头的`import`从mathlib导入实数理论. 简洁起见后面的例子里在前面有过的情况下就不写`import`了.

自己试着改改看! `ℝ`字符写作`\R`或`\real`然后按下空格键或tab键. 如果你在读取Lean文件时将鼠标悬停在符号上, VScode将向你显示可用于输入该符号的语法. 如果键盘没有容易按到的反斜杠, 则可以通过更改`lean.input.leader`来更改转义字符设置. 

当光标位于策略证明的中间时, Lean会在*Lean infoview*窗口中报告当前证明状态. 当你将光标移过证明的每一步时, 你可以看到状态的变化. Lean中的典型证明状态可能会是下面这样: 

```
1 goal
x y : ℕ,
h₁ : Prime x,
h₂ : ¬Even x,
h₃ : y > x
⊢ y ≥ 4
```

`⊢`前面的部分都是当前位置处我们所拥有的对象和假设, 称为语句集或者*语境*(context, 译者暂时并不知道这个词的标准译法). 本例中, 这里包含两个自然数对象`x`和`y`, 以及三个假设, 分别称作`h₁`,`h₂`,`h₃`(下标数字用`\1`,`\2`,`\3`等等来输入). Lean的语法要求在语境中每个假设都拥有一个名字, 叫什么都可以, 比如不下标的`h1`也可以. (实际上这是类型论的要求, 例如本例中`h₁`这个"名字"其实标记着类型为命题`Prime x`的项.)最后一行代表在当前状态下要证明的目标. 对于目标这个词, 一些人可能也会把整个Lean infoview的输出称为目标, 不过在特定上下文中不致混淆.

接下来做一些练习! 用`rw`策略替换掉下面的`sorry`. 为此再告诉你一个新技巧: 你可以用左箭头`←`(\l)来调转一个等式的方向, 从而让`rw`从另一边做替换操作. 例如, `rw ← mul_assoc a b c`会把目标里的`a * (b * c)`替换成`a * b * c`. 注意这里指的是`mul_assoc`等式的从右到左，它与目标的左边或右边无关。

```lean
example (a b c : ℝ) : c * b * a = b * (a * c) := by
  sorry

example (a b c : ℝ) : a * (b * c) = b * (a * c) := by
  sorry
```

你也可以不带参数使用诸如`mul_assoc`或者`mul_comm`这些等式. 这些情况下rewrite策略会识别它在目标中遇到的第一个匹配模式.

```lean
example (a b c : ℝ) : a * b * c = b * c * a := by
  rw [mul_assoc]
  rw [mul_comm]
```

你还可以只提供一部分参数, 例如`mul_comm a`识别所有形如`a * ?`或者`? * a`的模式. 下面的练习中你可以试试在第一个里面不给参数, 第二个里面只给一个参数.

```lean
example (a b c : ℝ) : a * (b * c) = b * (c * a) := by
  sorry

example (a b c : ℝ) : a * (b * c) = b * (a * c) := by
  sorry
```

你也可以`rw`局部语句集里的条件:

```lean
example (a b c d e f : ℝ) (h : a * b = c * d) (h' : e = f) : a * (b * e) = c * (d * f) := by
  rw [h']
  rw [← mul_assoc]
  rw [h]
  rw [mul_assoc]
```

试试看:
(第二个练习里面你可以使用定理`sub_self`, `sub_self a`代表等式`a - a = 0`.)

```lean
example (a b c d e f : ℝ) (h : b * c = e * f) : a * b * c * d = a * e * f * d := by
  sorry

example (a b c d : ℝ) (hyp : c = b * a - d) (hyp' : d = a * b) : c = 0 := by
  sorry
```

现在我们介绍Lean的一些有用的特性. 首先, 通过在方括号内列出相关等式, 可以用一行rewrite执行多个命令.

```lean
example (a b c d e f : ℝ) (h : a * b = c * d) (h' : e = f) : a * (b * e) = c * (d * f) := by
  rw [h', ← mul_assoc, h, mul_assoc]
```

将光标放在rewrite列表中的任意逗号后, 仍然可以看到进度. 

另一个技巧是我们可以在例子或定理之外一次性地声明变量. 当Lean在定理的陈述中看到它们时, 它会自动将它们包含进来. 

```lean
variable (a b c d e f : ℝ)

example (h : a * b = c * d) (h' : e = f) : a * (b * e) = c * (d * f) := by
  rw [h', ← mul_assoc, h, mul_assoc]
```

检查上述证明开头的策略状态, 可以发现Lean确实包含了相关变量, 而忽略了声明中没有出现的g. 我们可以把声明的范围放在一个`section ... end`块中做成类似其他编程语言中局部变量的效果. 最后, 回顾一下第一章, Lean为我们提供了一个命令来确定表达式的类型:

```lean
section
variable (a b c : ℝ)

#check a
#check a + b
#check (a : ℝ)
#check mul_comm a b
#check (mul_comm a b : a * b = b * a)
#check mul_assoc c a b
#check mul_comm a
#check mul_comm

end
```

`#check`命令对对象和命题都有效。在响应命令`#check a`时，Lean报告`a`的类型为`ℝ`。作为对命令`#check mul_comm a b`的响应，Lean报告`mul_comm a b`是事实`a * b = b * a`的证明。命令`#check (a:ℝ)`表明我们期望`a`的类型是`ℝ`，如果不是这样，Lean将引发一个错误。稍后我们将解释最后三个`#check`命令的输出，但与此同时，您可以查看它们，并尝试使用您自己的一些`#check`命令。

我们再举几个例子。定理`two_mul a`表示`2 * a = a + a`。定理`add_mul`和`mul_add`表示乘法对加法的分配性，定理`add_assoc`表示加法的结合律。使用`#check`命令查看精确的语句。

```lean
example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by
  rw [mul_add, add_mul, add_mul]
  rw [← add_assoc, add_assoc (a * a)]
  rw [mul_comm b a, ← two_mul]
```

虽然可以通过在编辑器中逐步检查来弄清楚这个证明中发生了什么，但很难单独阅读。Lean使用`calc`关键字提供了一种更结构化的方法来编写类似这样的证明。

```lean
example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b :=
  calc
    (a + b) * (a + b) = a * a + b * a + (a * b + b * b) := by
      rw [mul_add, add_mul, add_mul]
    _ = a * a + (b * a + a * b) + b * b := by
      rw [← add_assoc, add_assoc (a * a)]
    _ = a * a + 2 * (a * b) + b * b := by
      rw [mul_comm b a, ← two_mul]
```

以`calc`开头的表达式是一个证明项。`calc`表达式也可以在策略证明块中使用，Lean将其解释为使用证明项的结果来解决当前目标的指令。`calc`语法很挑剔，必须严格仿照上例格式使用下划线和对齐。Lean使用缩进来确定策略块或`calc`块开始和结束的地方。试着改变上面证明中的缩进，看看会发生什么。
*译者注--改变缩进好像没什么关系*

编写`calc`证明的一种方法是首先使用`sorry`策略填空，确保Lean接受中间步骤表达式，然后使用策略对各个步骤进行论证。

```lean
example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b :=
  calc
    (a + b) * (a + b) = a * a + b * a + (a * b + b * b) := by
      sorry
    _ = a * a + (b * a + a * b) + b * b := by
      sorry
    _ = a * a + 2 * (a * b) + b * b := by
      sorry
```
试试用两种方法证明以下等式：只用`rw`和用更结构化的`calc`。

```lean
example : (a + b) * (c + d) = a * c + a * d + b * c + b * d := by
  sorry
```

下面的练习有点挑战性。你可以用下面列出的定理。

```lean
example (a b : ℝ) : (a + b) * (a - b) = a ^ 2 - b ^ 2 := by
  sorry

#check pow_two a
#check mul_sub a b c
#check add_mul a b c
#check add_sub a b c
#check sub_sub a b c
#check add_zero a
```

我们还可以在语句集中的假设中执行重写。例如，`rw [mul_comm a b] at hyp`将假设`hyp`中的`a * b`替换为`b * a`。

```lean
example (a b c d : ℝ) (hyp : c = d * a + b) (hyp' : b = a * d) : c = 2 * a * d := by
  rw [hyp'] at hyp
  rw [mul_comm d a] at hyp
  rw [← two_mul (a * d)] at hyp
  rw [← mul_assoc 2 a d] at hyp
  exact hyp
```

最后一步中`exact`策略使用`hyp`来解决目标的原理是，到此`hyp`已经是目标本身了。

最后我们介绍一个Mathlib提供的强力自动化工具`ring`策略，它专门用来解决交换环中的等式，只要这些等式是完全由环公理导出的而不涉及别的假设。

```lean
example : c * b * a = b * (a * c) := by
  ring

example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by
  ring

example : (a + b) * (a - b) = a ^ 2 - b ^ 2 := by
  ring

example (hyp : c = d * a + b) (hyp' : b = a * d) : c = 2 * a * d := by
  rw [hyp, hyp']
  ring
```

`ring`策略通过`import Mathlib.Data.Real.Basic`导入，但下一节会看到它不止可以用在实数的计算上。它还可以通过`import Mathlib.Tactic`导入。我们会看到，对于其他常见的代数结构也有类似的策略。

`rw`有一种叫做`nth_rewrite`的变体，允许你替换目标表达式中具体到某个实例。匹配项从1开始计数，在下面的例子中`nth_rewrite 2 h`用`c`替换了第二个`a + b`。

```lean
example (a b c : ℕ) (h : a + b = c) : (a + b) * (a + b) = a * c + b * c := by
  nth_rw 2 [h]
  rw [add_mul]
```

## 2.2. 证明代数结构中的等式

数学中，环由一个对象集合$R$、运算$+ ×$、常数$0,1$、求逆运算$x ↦ -x$并满足：

- $R$与$+$构成阿贝尔群，$0$是加法单位元，负数是逆。
- $1$是乘法单位元，乘法满足结合律和对加法的分配律。

在Lean中，对象集合被表示为类型`R`。环公理如下:

```lean
variable (R : Type*) [Ring R]

#check (add_assoc : ∀ a b c : R, a + b + c = a + (b + c))
#check (add_comm : ∀ a b : R, a + b = b + a)
#check (zero_add : ∀ a : R, 0 + a = a)
#check (add_left_neg : ∀ a : R, -a + a = 0)
#check (mul_assoc : ∀ a b c : R, a * b * c = a * (b * c))
#check (mul_one : ∀ a : R, a * 1 = a)
#check (one_mul : ∀ a : R, 1 * a = a)
#check (mul_add : ∀ a b c : R, a * (b + c) = a * b + a * c)
#check (add_mul : ∀ a b c : R, (a + b) * c = a * c + b * c)
```

一会儿再讲第一行的方括号是什么意思，现在你只需要知道我们声明了一个类型`R`和`R`上的环结构。这样我们就可以表示一般的环中的元素并使用环的定理库。

前一节用过上面的一些定理，所以你应该感觉很熟悉。Lean不止能在例如自然数和整数这样具体的数学结构上证明东西，也可以在环这样抽象的公理化的结构上证明东西。Lean支持抽象和具体结构的通用推理，并且有能力识别符合公理的实例。任何关于环的定理都可以应用于具体的环，如整数`ℤ`、有理数`ℚ`、复数`ℂ`，和抽象的环，如任何有序环或任何域。

然而，并不是所有实数的重要性质在任意环中都成立。例如，实数乘法是可交换的，但一般情况下并不成立。例如实数矩阵构成的环的乘法通常不能交换。如果我们声明`R`是一个交换环`CommRing`，上一节中的所有关于`ℝ`定理在`R`中仍然成立。

```lean
variable (R : Type*) [CommRing R]
variable (a b c d : R)

example : c * b * a = b * (a * c) := by ring

example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by ring

example : (a + b) * (a - b) = a ^ 2 - b ^ 2 := by ring

example (hyp : c = d * a + b) (hyp' : b = a * d) : c = 2 * a * d := by
  rw [hyp, hyp']
  ring
```

别的证明也都不需要变，你可以自己试试看。当证明很短时，比如你只用了一个`ring`或者`linarith`或者`sorry`，你可以把它们写进`by`的同一行里。好的证明写手需要平衡简洁性和可读性。

本节里面我们会证明更多环定理，它们基本上都在Mathlib里面，看完这一节你会对Mathlib里面的东西更熟悉。同时这也是训练你的证明能力。

Lean提供了类似于别的编程语言中的“局域变量”的变量名组织机制。通过命令`namespace bar`创建一个命名空间`bar`并引入定义或者定理`foo`，你在命名空间外面引用它时全名为`bar.foo`。命令`open bar`可以打开这个命名空间，此时你可以用短名字`foo`。下面我们为了不与Mathlib中的定理名冲突，我们打开一个名为`MyRing`的命名空间。

下面的例子证明了`add_zero`和`add_right_neg`，所以它们不需要作为环公理。

```lean
namespace MyRing
variable {R : Type*} [Ring R]

theorem add_zero (a : R) : a + 0 = a := by rw [add_comm, zero_add]

theorem add_right_neg (a : R) : a + -a = 0 := by rw [add_comm, add_left_neg]

#check MyRing.add_zero
#check add_zero

end MyRing
```

我们重新证明了库中的定理，但是我们可以继续使用库中的版本。但是下面的练习中请不要作弊，我们只能用我们之前证明过的定理。

(如果你仔细注意的话，你可能已经注意到我们把`(R: Type*)`中的圆括号改成了`{R: Type*}`中的花括号。这里声明`R`是一个*隐式参数*。稍后会解释这意味着什么。)

下面这个定理很有用：

```lean
theorem neg_add_cancel_left (a b : R) : -a + (a + b) = b := by
  rw [← add_assoc, add_left_neg, zero_add]
```

证明它的配套版本：

```lean
-- 译者注：记得先设置namespace
theorem add_neg_cancel_right (a b : R) : a + b + -b = a := by
  sorry
```

然后用它们证明下面几个（最佳方案仅需三次重写）：

```lean
theorem add_left_cancel {a b c : R} (h : a + b = a + c) : b = c := by
  sorry

theorem add_right_cancel {a b c : R} (h : a + b = c + b) : a = c := by
  sorry
```

现在解释一下花括号的意思。假设你现在语句集里面拥有变量`a`、`b`、`c`和一个假设`h : a + b = a + c`，然后你想得到结论`b = c`。在Lean中，定理可以应用于假设和事实，就像将它们应用于对象一样，因此你可能会认为`add_left_cancel a b c h`是事实`b = c`的证明。但其实明确地写出`a b c`是多余的，因为假设`h`的形式就限定了它们正是我们想使用的对象。现下输入几个额外的字符并不麻烦，但是更复杂的表达式中就会很繁琐。Lean支持把参数标记为隐式，这意味着它们可以且应该被省略，能通过后面的的命题和假设中推断出来。`{a b c: R}`中的花括号正是这种隐式参数标记。因此根据定理的表述，正确的表达式是`add_left_cancel h`。

下面演示个新玩意儿，让我们从环公理中证明a * 0 = 0。

```lean
theorem mul_zero (a : R) : a * 0 = 0 := by
  have h : a * 0 + a * 0 = a * 0 + 0 := by
    rw [← mul_add, add_zero, add_zero]
  rw [add_left_cancel h]
```

你通过`have`策略引入了一个辅助性新目标，`a * 0 + a * 0 = a * 0 + 0`，与原始目标具有相同的语境。这个目标下的“子证明”块需要缩进。证出这个子目标之后我们就多了一个新的命题`h`，可以用于证明原目标。这里我们看到`add_left_cancel h`的结果恰好就是原目标。

我们同样可以使用`apply add_left_cancel h`或`exact add_left_cancel h`来结束证明。`exact`策略将能够完整证明当前目标的证明项作为参数，而不创建任何新目标。`apply`策略是一种变体，它的论证不一定是一个完整的证明。缺失的部分要么由Lean自动推断，要么成为需要证明的新目标。虽然`exact`策略在技术上是多余的，因为它严格来说不如`apply`强大，但它增加了可读性。

乘法不一定可交换，所以下面的定理也需要证。

```lean
theorem zero_mul (a : R) : 0 * a = 0 := by
  sorry
```

更多练习：

```lean
theorem neg_eq_of_add_eq_zero {a b : R} (h : a + b = 0) : -a = b := by
  sorry

theorem eq_neg_of_add_eq_zero {a b : R} (h : a + b = 0) : a = -b := by
  sorry

theorem neg_zero : (-0 : R) = 0 := by
  apply neg_eq_of_add_eq_zero
  rw [add_zero]

theorem neg_neg (a : R) : - -a = a := by
  sorry
```

我们必须在第三个定理中指定`(-0 : R)`, 因为Lean不知道我们想到的是哪个`0`，默认情况下它是自然数。

在Lean中，环上的减法等于加上加法的逆。

```lean
example (a b : R) : a - b = a + -b :=
  sub_eq_add_neg a b
```

实数的减法就是被如此定义的，因此：

```lean
example (a b : ℝ) : a - b = a + -b :=
  rfl

example (a b : ℝ) : a - b = a + -b := by
  rfl
```

`rfl`是自反性（reflexivity）的缩写。第一个例子中当它作为`a - b = a + -b`的证明项，Lean展开定义并验证两边是相同的。第二个例子中`rfl`策略也是如此。这是在Lean的基础逻辑中所谓的定义相等的一个例子。这意味着不仅可以用`sub_eq_add_neg`重写来替换`a - b = a + -b`，而且在某些情况下，当处理实数时，您可以互换使用方程的两边。例如，您现在有足够的信息来证明上一节中的`self_sub`定理:

```lean
theorem self_sub (a : R) : a - a = 0 := by
  sorry
```

你可以使用`rw`来证，不过如果不是任意环`R`而是实数的话，你也可以用`apply`或者`exact`。

Lean知道`1 + 1 = 2`对任何环都成立。你可以用它来证明上一节中的定理`two_mul`。

```lean
theorem one_add_one_eq_two : 1 + 1 = (2 : R) := by
  norm_num

theorem two_mul (a : R) : 2 * a = a + a := by
  sorry
```

上面的一些定理并不需要环结构甚至加法交换律，有群结构就够了，群公理是下面这些：

```lean
variable (A : Type*) [AddGroup A]

#check (add_assoc : ∀ a b c : A, a + b + c = a + (b + c))
#check (zero_add : ∀ a : A, 0 + a = a)
#check (add_left_neg : ∀ a : A, -a + a = 0)
```

群运算可交换的话习惯上用加号(但是这只是习惯而已，`AddGroup`并不真的可交换)，否则用乘号。Lean提供乘法版本`Group`和加法版本`AddGroup`，以及它们的可交换版本`CommGroup`和`AddCommGroup`。

```lean
variable {G : Type*} [Group G]

#check (mul_assoc : ∀ a b c : G, a * b * c = a * (b * c))
#check (one_mul : ∀ a : G, 1 * a = a)
#check (mul_left_inv : ∀ a : G, a⁻¹ * a = 1)
```

试试用这些群公理证明以下命题。你可以引入一些引理。

```lean
theorem mul_right_inv (a : G) : a * a⁻¹ = 1 := by
  sorry

theorem mul_one (a : G) : a * 1 = a := by
  sorry

theorem mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
  sorry
```

一步一步用这些定理做证明非常麻烦，所以在这些代数结构上Mathlib提供了类似`ring`的策略：`group`用于非交换的乘法群，`abel`用于可交换加法群，`noncomm_ring`用于非交换环。代数结构`Ring`和`CommRing`分别对应的自动化策略被称做`noncomm_ring`和`ring`，这似乎很奇怪。这在一定程度上是由于历史原因，但也因为使用更短的名称来处理交换环的策略更方便，因为它使用得更频繁。

## 2.3. 使用定理和引理

重写对于证明等式很有用，但是对于其他类型的定理呢？例如，我们如何证明一个不等式，比如在$b ≤ c$时$a + e ^ b ≤ a + e ^ c$？ 本节我们会着重使用`apply`和`exact`。

考虑库定理`le_refl`和`le_trans`：

```lean
variable (a b c : ℝ)

#check (le_refl : ∀ a : ℝ, a ≤ a)
#check (le_trans : a ≤ b → b ≤ c → a ≤ c)
```

`→`是右结合的，因此`le_trans`应该被解释为`a ≤ b → (b ≤ c → a ≤ c)`。详细规则在3.1节中解释。标准库设计者已经将`le_trans`中的`a`, `b`和`c`设置为隐式参数，也就是在使用时从语境中推断。(强制显式参数将在后面讨论)。例如，当假设`h : a ≤ b`和`h' : b ≤ c`在语句集中时，以下所有语句都有效:
```lean
variable (h : a ≤ b) (h' : b ≤ c)

#check (le_refl : ∀ a : Real, a ≤ a)
#check (le_refl a : a ≤ a)
#check (le_trans : a ≤ b → b ≤ c → a ≤ c)
#check (le_trans h : b ≤ c → a ≤ c)
#check (le_trans h h' : a ≤ c)
```

`apply`策略对一般陈述或暗示进行证明，试图将结论与当前目标相匹配，并将假设(如果有的话)作为新目标。如果给定的证明与目标完全匹配(模定义等式)，则可以使用`exact`策略而不是`apply`。所以，所有这些工作:

The apply tactic takes a proof of a general statement or implication, tries to match the conclusion with the current goal, and leaves the hypotheses, if any, as new goals. If the given proof matches the goal exactly (modulo definitional equality), you can use the exact tactic instead of apply. So, all of these work:

```lean
example (x y z : ℝ) (h₀ : x ≤ y) (h₁ : y ≤ z) : x ≤ z := by
  apply le_trans
  · apply h₀
  . apply h₁

example (x y z : ℝ) (h₀ : x ≤ y) (h₁ : y ≤ z) : x ≤ z := by
  apply le_trans h₀
  apply h₁

example (x y z : ℝ) (h₀ : x ≤ y) (h₁ : y ≤ z) : x ≤ z :=
  le_trans h₀ h₁

example (x : ℝ) : x ≤ x := by
  apply le_refl

example (x : ℝ) : x ≤ x :=
  le_refl x
```

在第一个示例中，`apply le_trans` 创建两个目标，我们使用点来指示每个证明的开始位置。 这些点是可选的，但它们用于聚焦目标： 在点引入的块中，只有一个目标可见， 并且必须在区块结束之前完成。 在这里，我们通过用另一个点开始一个新块来结束第一个块。 我们也可以减少缩进。 在第四个示例和最后一个示例中， 我们避免完全进入 `tactic` 模式：`le_transle_trans h₀ h₁` 和 `le_refl x` 是我们需要的证明项。

这里还有几个库中的定理。
In the first example, applying le_trans creates two goals, and we use the dots to indicate where the proof of each begins. The dots are optional, but they serve to focus the goal: within the block introduced by the dot, only one goal is visible, and it must be completed before the end of the block. Here we end the first block by starting a new one with another dot. We could just as well have decreased the indentation. In the fourth example and in the last example, we avoid going into tactic mode entirely: le_trans h₀ h₁ and le_refl x are the proof terms we need.

Here are a few more library theorems:

```lean
#check (le_refl : ∀ a, a ≤ a)
#check (le_trans : a ≤ b → b ≤ c → a ≤ c)
#check (lt_of_le_of_lt : a ≤ b → b < c → a < c)
#check (lt_of_lt_of_le : a < b → b ≤ c → a < c)
#check (lt_trans : a < b → b < c → a < c)
```

利用这些定理和`apply`和`exact`策略来证明下面的问题：

```lean
example (h₀ : a ≤ b) (h₁ : b < c) (h₂ : c ≤ d) (h₃ : d < e) : a < e := by
  sorry
```

实际上Lean有一个自动化策略来证明这类问题：

```lean
example (h₀ : a ≤ b) (h₁ : b < c) (h₂ : c ≤ d) (h₃ : d < e) : a < e := by
  linarith
```

`linarith`策略用于处理线性算术。

```lean
example (h : 2 * a ≤ 3 * b) (h' : 1 ≤ a) (h'' : d = 2) : d + a ≤ 5 * b := by
  linarith
```

除了上下文中的方程和不等式之外，`linarith` 还将使用您作为参数传递的其他不等式。 在下一个示例中，`exp_le_exp.mpr h'` 是 `exp b ≤ exp c` 的证明，我们稍后将对此进行解释。 请注意，在 Lean 中，我们用 `f x` 来表示将函数 `f` 应用于参数 `x`, 这与我们用 `h x` 来表示将事实或定理 `h` 应用到参数 `x ` 完全相同。 括号仅用于复合参数，如 `f (x + y)` 。 如果没有括号，`f x + y` 将被解析为 `(f x) + y`。

In addition to equations and inequalities in the context, linarith will use additional inequalities that you pass as arguments. In the next example, exp_le_exp.mpr h' is a proof of exp b ≤ exp c, as we will explain in a moment. Notice that, in Lean, we write f x to denote the application of a function f to the argument x, exactly the same way we write h x to denote the result of applying a fact or theorem h to the argument x. Parentheses are only needed for compound arguments, as in f (x + y). Without the parentheses, f x + y would be parsed as (f x) + y.

```lean
example (h : 1 ≤ a) (h' : b ≤ c) : 2 + a + exp b ≤ 3 * a + exp c := by
  linarith [exp_le_exp.mpr h']
```

这里列出更多库定理，可以用于实数上的不等式：

```lean
#check (exp_le_exp : exp a ≤ exp b ↔ a ≤ b)
#check (exp_lt_exp : exp a < exp b ↔ a < b)
#check (log_le_log : 0 < a → 0 < b → (log a ≤ log b ↔ a ≤ b))
#check (log_lt_log : 0 < a → a < b → log a < log b)
#check (add_le_add : a ≤ b → c ≤ d → a + c ≤ b + d)
#check (add_le_add_left : a ≤ b → ∀ c, c + a ≤ c + b)
#check (add_le_add_right : a ≤ b → ∀ c, a + c ≤ b + c)
#check (add_lt_add_of_le_of_lt : a ≤ b → c < d → a + c < b + d)
#check (add_lt_add_of_lt_of_le : a < b → c ≤ d → a + c < b + d)
#check (add_lt_add_left : a < b → ∀ c, c + a < c + b)
#check (add_lt_add_right : a < b → ∀ c, a + c < b + c)
#check (add_nonneg : 0 ≤ a → 0 ≤ b → 0 ≤ a + b)
#check (add_pos : 0 < a → 0 < b → 0 < a + b)
#check (add_pos_of_pos_of_nonneg : 0 < a → 0 ≤ b → 0 < a + b)
#check (exp_pos : ∀ a, 0 < exp a)
#check add_le_add_left
```

`exp_le_exp` 、`exp_lt_exp` 和 `log_le_log` 等定理使用双蕴含，表示短语“当且仅当”。(你可以在 VS Code 中输入 `\lr` 或者 `\iff`)。我们将在下一章更详细地讨论这个连接词。这样的定理可以与 `rw` 一起使用，将目标重写为等效的目标:

Some of the theorems, exp_le_exp, exp_lt_exp, and log_le_log use a bi-implication, which represents the phrase “if and only if.” (You can type it in VS Code with \lr of \iff). We will discuss this connective in greater detail in the next chapter. Such a theorem can be used with rw to rewrite a goal to an equivalent one:

```lean
example (h : a ≤ b) : exp a ≤ exp b := by
  rw [exp_le_exp]
  exact h
```
然而，在本节中，我们将使用这样一个事实，即如果 `h : A ↔ B` 是这样一个等价，则 `h.mp` 建立正向 `A → B` ，而 `h.mpr` 建立反向 `B → A` 。这里，`mp` 代表"肯定前件式"，mpr代表"肯定前件式的反向"。如果愿意，还可以分别为 `h.mp` 和 `h.mpr` 使用 `h.1` 和 `h.2` 。因此，下面的证明是有效的:

In this section, however, we will use the fact that if h : A ↔ B is such an equivalence, then h.mp establishes the forward direction, A → B, and h.mpr establishes the reverse direction, B → A. Here, mp stands for “modus ponens” and mpr stands for “modus ponens reverse.” You can also use h.1 and h.2 for h.mp and h.mpr, respectively, if you prefer. Thus the following proof works:

```lean
example (h₀ : a ≤ b) (h₁ : c < d) : a + exp c + e < b + exp d + e := by
  apply add_lt_add_of_lt_of_le
  · apply add_lt_add_of_le_of_lt h₀
    apply exp_lt_exp.mpr h₁
  apply le_refl

```
第一行，`apply add_lt_add_of_lt_of_le` 创建了两个目标，我们再次使用一个点将第一个证明与第二个证明分开。

试试下面的例子。中间的示例向您展示了 `norm_num` 策略可用于解决具体的数字目标。

The first line, apply add_lt_add_of_lt_of_le, creates two goals, and once again we use a dot to separate the proof of the first from the proof of the second.

Try the following examples on your own. The example in the middle shows you that the norm_num tactic can be used to solve concrete numeric goals.

```lean
example (h₀ : d ≤ e) : c + exp (a + d) ≤ c + exp (a + e) := by sorry

example : (0 : ℝ) < 1 := by norm_num

example (h : a ≤ b) : log (1 + exp a) ≤ log (1 + exp b) := by
  have h₀ : 0 < 1 + exp a := by sorry
  have h₁ : 0 < 1 + exp b := by sorry
  apply (log_le_log h₀ h₁).mpr
  sorry
```

从这些例子中应该认清的是，找到您需要的库定理是形式化的重要组成部分。您可以参考以下方式：

您可以在 GitHub 存储库中浏览 Mathlib。

您可以在Mathlib网页上使用API文档。

您可以根据编辑器中的 Mathlib 命名惯例和 `Ctrl-空格` 来猜测定理名称（或 Mac 键盘上的 `Cmd-空格` ）。在 Lean 中，一个名为 `A_of_B_of_C` 的定理从形式为B和C的假设中建立了形式A的东西，其中 A 、B 和 C 近似于我们大声读出目标的方式。因此，一个包含形如 `x + y ≤ ...` 的定理可能会以 `add_le` 开头。键入 `add_le` 并使用快捷键 `Ctrl-空格` 将为您提供一些有用的选择。请注意，按两次 `Ctrl-空格` 将显示更多可用的信息。

如果右键单击VS Code中现有的定理名称，编辑器将显示一个菜单，其中包含跳到定义定理的文件的选项，您可以在附近找到类似的定理。
你可以使用应用程序吗？策略，试图在库中找到相关的定理。

From these examples, it should be clear that being able to find the library theorems you need constitutes an important part of formalization. There are a number of strategies you can use:

You can browse Mathlib in its GitHub repository.

You can use the API documentation on the Mathlib web pages.

You can rely on Mathlib naming conventions and Ctrl-space completion in the editor to guess a theorem name (or Cmd-space on a Mac keyboard). In Lean, a theorem named A_of_B_of_C establishes something of the form A from hypotheses of the form B and C, where A, B, and C approximate the way we might read the goals out loud. So a theorem establishing something like x + y ≤ ... will probably start with add_le. Typing add_le and hitting Ctrl-space will give you some helpful choices. Note that hitting Ctrl-space twice displays more information about the available completions.

If you right-click on an existing theorem name in VS Code, the editor will show a menu with the option to jump to the file where the theorem is defined, and you can find similar theorems nearby.

You can use the apply? tactic, which tries to find the relevant theorem in the library.

```lean
example : 0 ≤ a ^ 2 := by
  -- apply?
  exact sq_nonneg a
```


To try out apply? in this example, delete the exact command and uncomment the previous line. Using these tricks, see if you can find what you need to do the next example:

```lean
example (h : a ≤ b) : c - exp b ≤ c - exp a := by
  sorry
```


Using the same tricks, confirm that linarith instead of apply? can also finish the job.

Here is another example of an inequality:

```lean
example : 2 * a * b ≤ a ^ 2 + b ^ 2 := by
  have h : 0 ≤ a ^ 2 - 2 * a * b + b ^ 2
  calc
    a ^ 2 - 2 * a * b + b ^ 2 = (a - b) ^ 2 := by ring
    _ ≥ 0 := by apply pow_two_nonneg

  calc
    2 * a * b = 2 * a * b + 0 := by ring
    _ ≤ 2 * a * b + (a ^ 2 - 2 * a * b + b ^ 2) :=
      add_le_add (le_refl _) h
    _ = a ^ 2 + b ^ 2 := by ring
```


Mathlib tends to put spaces around binary operations like * and ^, but in this example, the more compressed format increases readability. There are a number of things worth noticing. First, an expression s ≥ t is definitionally equivalent to t ≤ s. In principle, this means one should be able to use them interchangeably. But some of Lean’s automation does not recognize the equivalence, so Mathlib tends to favor ≤ over ≥. Second, we have used the ring tactic extensively. It is a real timesaver! Finally, notice that in the second line of the second calc proof, instead of writing by exact add_le_add (le_refl _) h, we can simply write the proof term add_le_add (le_refl _) h.

In fact, the only cleverness in the proof above is figuring out the hypothesis h. Once we have it, the second calculation involves only linear arithmetic, and linarith can handle it:

```lean
example : 2 * a * b ≤ a ^ 2 + b ^ 2 := by
  have h : 0 ≤ a ^ 2 - 2 * a * b + b ^ 2
  calc
    a ^ 2 - 2 * a * b + b ^ 2 = (a - b) ^ 2 := by ring
    _ ≥ 0 := by apply pow_two_nonneg
  linarith
How nice! We challenge you to use these ideas to prove the following theorem. You can use the theorem abs_le'.mpr.
```


```lean
example : |a * b| ≤ (a ^ 2 + b ^ 2) / 2 := by
  sorry
#check abs_le'.mpr
```



If you managed to solve this, congratulations! You are well on your way to becoming a master formalizer.

## 2.4. apply和rw的更多例子

`min`函数在实数中被下面这三个命题来描述：

```lean
#check (min_le_left a b : min a b ≤ a)
#check (min_le_right a b : min a b ≤ b)
#check (le_min : c ≤ a → c ≤ b → c ≤ min a b)
```


Can you guess the names of the theorems that characterize max in a similar way?

Notice that we have to apply min to a pair of arguments a and b by writing min a b rather than min (a, b). Formally, min is a function of type ℝ → ℝ → ℝ. When we write a type like this with multiple arrows, the convention is that the implicit parentheses associate to the right, so the type is interpreted as ℝ → (ℝ → ℝ). The net effect is that if a and b have type ℝ then min a has type ℝ → ℝ and min a b has type ℝ, so min acts like a function of two arguments, as we expect. Handling multiple arguments in this way is known as currying, after the logician Haskell Curry.

The order of operations in Lean can also take some getting used to. Function application binds tighter than infix operations, so the expression min a b + c is interpreted as (min a b) + c. With time, these conventions will become second nature.

Using the theorem le_antisymm, we can show that two real numbers are equal if each is less than or equal to the other. Using this and the facts above, we can show that min is commutative:

```lean
example : min a b = min b a := by
  apply le_antisymm
  · show min a b ≤ min b a
    apply le_min
    · apply min_le_right
    apply min_le_left
  · show min b a ≤ min a b
    apply le_min
    · apply min_le_right
    apply min_le_left
```


Here we have used dots to separate proofs of different goals. Our usage is inconsistent: at the outer level, we use dots and indentation for both goals, whereas for the nested proofs, we use dots only until a single goal remains. Both conventions are reasonable and useful. We also use the show tactic to structure the proof and indicate what is being proved in each block. The proof still works without the show commands, but using them makes the proof easier to read and maintain.

It may bother you that the proof is repetitive. To foreshadow skills you will learn later on, we note that one way to avoid the repetition is to state a local lemma and then use it:

```lean
example : min a b = min b a := by
  have h : ∀ x y : ℝ, min x y ≤ min y x := by
    intro x y
    apply le_min
    apply min_le_right
    apply min_le_left
  apply le_antisymm
  apply h
  apply h
```


We will say more about the universal quantifier in Section 3.1, but suffice it to say here that the hypothesis h says that the desired inequality holds for any x and y, and the intro tactic introduces an arbitrary x and y to establish the conclusion. The first apply after le_antisymm implicitly uses h a b, whereas the second one uses h b a.

Another solution is to use the repeat tactic, which applies a tactic (or a block) as many times as it can.

```lean
example : min a b = min b a := by
  apply le_antisymm
  repeat
    apply le_min
    apply min_le_right
    apply min_le_left
```

In any case, whether or not you use these tricks, we encourage you to prove the following:

```lean
example : max a b = max b a := by
  sorry
example : min (min a b) c = min a (min b c) := by
  sorry
```


Of course, you are welcome to prove the associativity of max as well.

It is an interesting fact that min distributes over max the way that multiplication distributes over addition, and vice-versa. In other words, on the real numbers, we have the identity min a (max b c) ≤ max (min a b) (min a c) as well as the corresponding version with max and min switched. But in the next section we will see that this does not follow from the transitivity and reflexivity of ≤ and the characterizing properties of min and max enumerated above. We need to use the fact that ≤ on the real numbers is a total order, which is to say, it satisfies ∀ x y, x ≤ y ∨ y ≤ x. Here the disjunction symbol, ∨, represents “or”. In the first case, we have min x y = x, and in the second case, we have min x y = y. We will learn how to reason by cases in Section 3.5, but for now we will stick to examples that don’t require the case split.

Here is one such example:

```lean
theorem aux : min a b + c ≤ min (a + c) (b + c) := by
  sorry
example : min a b + c = min (a + c) (b + c) := by
  sorry
```


It is clear that aux provides one of the two inequalities needed to prove the equality, but applying it to suitable values yields the other direction as well. As a hint, you can use the theorem add_neg_cancel_right and the linarith tactic.

Lean’s naming convention is made manifest in the library’s name for the triangle inequality:

```lean
#check (abs_add : ∀ a b : ℝ, |a + b| ≤ |a| + |b|)
```


Use it to prove the following variant:

```lean
example : |a| - |b| ≤ |a - b| :=
  sorry
end
```


See if you can do this in three lines or less. You can use the theorem sub_add_cancel.

Another important relation that we will make use of in the sections to come is the divisibility relation on the natural numbers, x ∣ y. Be careful: the divisibility symbol is not the ordinary bar on your keyboard. Rather, it is a unicode character obtained by typing \| in VS Code. By convention, Mathlib uses dvd to refer to it in theorem names.

```lean
example (h₀ : x ∣ y) (h₁ : y ∣ z) : x ∣ z :=
  dvd_trans h₀ h₁
```


```lean
example : x ∣ y * x * z := by
  apply dvd_mul_of_dvd_left
  apply dvd_mul_left
```
```lean
example : x ∣ x ^ 2 := by
   apply dvd_mul_left
```



In the last example, the exponent is a natural number, and applying dvd_mul_left forces Lean to expand the definition of x^2 to x * x^1. See if you can guess the names of the theorems you need to prove the following:

```lean
example (h : x ∣ w) : x ∣ y * (x * z) + x ^ 2 + w ^ 2 := by
  sorry
end
```

With respect to divisibility, the greatest common divisor, gcd, and least common multiple, lcm, are analogous to min and max. Since every number divides 0, 0 is really the greatest element with respect to divisibility:


```lean
variable (m n : ℕ)

#check (Nat.gcd_zero_right n : Nat.gcd n 0 = n)
#check (Nat.gcd_zero_left n : Nat.gcd 0 n = n)
#check (Nat.lcm_zero_right n : Nat.lcm n 0 = 0)
#check (Nat.lcm_zero_left n : Nat.lcm 0 n = 0)
```


See if you can guess the names of the theorems you will need to prove the following:

```lean
example : Nat.gcd m n = Nat.gcd n m := by
  sorry
```



Hint: you can use dvd_antisymm, but if you do, Lean will complain that the expression is ambiguous between the generic theorem and the version Nat.dvd_antisymm, the one specifically for the natural numbers. You can use _root_.dvd_antisymm to specify the generic one; either one will work.

## 2.5. 证明Proving Facts about Algebraic Structures
In Section 2.2, we saw that many common identities governing the real numbers hold in more general classes of algebraic structures, such as commutative rings. We can use any axioms we want to describe an algebraic structure, not just equations. For example, a partial order consists of a set with a binary relation that is reflexive and transitive, like ≤ on the real numbers. Lean knows about partial orders:

```lean
variable {α : Type*} [PartialOrder α]
variable (x y z : α)

#check x ≤ y
#check (le_refl x : x ≤ x)
#check (le_trans : x ≤ y → y ≤ z → x ≤ z)
```


Here we are adopting the Mathlib convention of using letters like α, β, and γ (entered as \a, \b, and \g) for arbitrary types. The library often uses letters like R and G for the carries of algebraic structures like rings and groups, respectively, but in general Greek letters are used for types, especially when there is little or no structure associated with them.

Associated to any partial order, ≤, there is also a strict partial order, <, which acts somewhat like < on the real numbers. Saying that x is less than y in this order is equivalent to saying that it is less-than-or-equal to y and not equal to y.

```lean
#check x < y
#check (lt_irrefl x : ¬x < x)
#check (lt_trans : x < y → y < z → x < z)
#check (lt_of_le_of_lt : x ≤ y → y < z → x < z)
#check (lt_of_lt_of_le : x < y → y ≤ z → x < z)

example : x < y ↔ x ≤ y ∧ x ≠ y :=
  lt_iff_le_and_ne
```


In this example, the symbol ∧ stands for “and,” the symbol ¬ stands for “not,” and x ≠ y abbreviates ¬ (x = y). In Chapter 3, you will learn how to use these logical connectives to prove that < has the properties indicated.

A lattice is a structure that extends a partial order with operations ⊓ and ⊔ that are analogous to min and max on the real numbers:

```lean
variable {α : Type*} [Lattice α]
variable (x y z : α)

#check x ⊓ y
#check (inf_le_left : x ⊓ y ≤ x)
#check (inf_le_right : x ⊓ y ≤ y)
#check (le_inf : z ≤ x → z ≤ y → z ≤ x ⊓ y)
#check x ⊔ y
#check (le_sup_left : x ≤ x ⊔ y)
#check (le_sup_right : y ≤ x ⊔ y)
#check (sup_le : x ≤ z → y ≤ z → x ⊔ y ≤ z)
```


The characterizations of ⊓ and ⊔ justify calling them the greatest lower bound and least upper bound, respectively. You can type them in VS code using \glb and \lub. The symbols are also often called then infimum and the supremum, and Mathlib refers to them as inf and sup in theorem names. To further complicate matters, they are also often called meet and join. Therefore, if you work with lattices, you have to keep the following dictionary in mind:

⊓ is the greatest lower bound, infimum, or meet.

⊔ is the least upper bound, supremum, or join.

Some instances of lattices include:

min and max on any total order, such as the integers or real numbers with ≤

∩ and ∪ on the collection of subsets of some domain, with the ordering ⊆

∧ and ∨ on boolean truth values, with ordering x ≤ y if either x is false or y is true

gcd and lcm on the natural numbers (or positive natural numbers), with the divisibility ordering, ∣

the collection of linear subspaces of a vector space, where the greatest lower bound is given by the intersection, the least upper bound is given by the sum of the two spaces, and the ordering is inclusion

the collection of topologies on a set (or, in Lean, a type), where the greatest lower bound of two topologies consists of the topology that is generated by their union, the least upper bound is their intersection, and the ordering is reverse inclusion

You can check that, as with min / max and gcd / lcm, you can prove the commutativity and associativity of the infimum and supremum using only their characterizing axioms, together with le_refl and le_trans.

```lean
example : x ⊓ y = y ⊓ x := by
  sorry

example : x ⊓ y ⊓ z = x ⊓ (y ⊓ z) := by
  sorry

example : x ⊔ y = y ⊔ x := by
  sorry

example : x ⊔ y ⊔ z = x ⊔ (y ⊔ z) := by
  sorry
```


You can find these theorems in the Mathlib as inf_comm, inf_assoc, sup_comm, and sup_assoc, respectively.

Another good exercise is to prove the absorption laws using only those axioms:

```lean
theorem absorb1 : x ⊓ (x ⊔ y) = x := by
  sorry

theorem absorb2 : x ⊔ x ⊓ y = x := by
  sorry
```


These can be found in Mathlib with the names inf_sup_self and sup_inf_self.

A lattice that satisfies the additional identities x ⊓ (y ⊔ z) = (x ⊓ y) ⊔ (x ⊓ z) and x ⊔ (y ⊓ z) = (x ⊔ y) ⊓ (x ⊔ z) is called a distributive lattice. Lean knows about these too:

```lean
variable {α : Type*} [DistribLattice α]
variable (x y z : α)

#check (inf_sup_left : x ⊓ (y ⊔ z) = x ⊓ y ⊔ x ⊓ z)
#check (inf_sup_right : (x ⊔ y) ⊓ z = x ⊓ z ⊔ y ⊓ z)
#check (sup_inf_left : x ⊔ y ⊓ z = (x ⊔ y) ⊓ (x ⊔ z))
#check (sup_inf_right : x ⊓ y ⊔ z = (x ⊔ z) ⊓ (y ⊔ z))
```


The left and right versions are easily shown to be equivalent, given the commutativity of ⊓ and ⊔. It is a good exercise to show that not every lattice is distributive by providing an explicit description of a nondistributive lattice with finitely many elements. It is also a good exercise to show that in any lattice, either distributivity law implies the other:

```lean
variable {α : Type*} [Lattice α]
variable (a b c : α)

example (h : ∀ x y z : α, x ⊓ (y ⊔ z) = x ⊓ y ⊔ x ⊓ z) : a ⊔ b ⊓ c = (a ⊔ b) ⊓ (a ⊔ c) := by
  sorry

example (h : ∀ x y z : α, x ⊔ y ⊓ z = (x ⊔ y) ⊓ (x ⊔ z)) : a ⊓ (b ⊔ c) = a ⊓ b ⊔ a ⊓ c := by
  sorry
```


It is possible to combine axiomatic structures into larger ones. For example, a strict ordered ring consists of a commutative ring together with a partial order on the carrier satisfying additional axioms that say that the ring operations are compatible with the order:

```lean
variable {R : Type*} [StrictOrderedRing R]
variable (a b c : R)

#check (add_le_add_left : a ≤ b → ∀ c, c + a ≤ c + b)
#check (mul_pos : 0 < a → 0 < b → 0 < a * b)
```


Chapter 3 will provide the means to derive the following from mul_pos and the definition of <:

#check (mul_nonneg : 0 ≤ a → 0 ≤ b → 0 ≤ a * b)
It is then an extended exercise to show that many common facts used to reason about arithmetic and the ordering on the real numbers hold generically for any ordered ring. Here are a couple of examples you can try, using only properties of rings, partial orders, and the facts enumerated in the last two examples:

```lean
example (h : a ≤ b) : 0 ≤ b - a := by
  sorry

example (h: 0 ≤ b - a) : a ≤ b := by
  sorry

example (h : a ≤ b) (h' : 0 ≤ c) : a * c ≤ b * c := by
  sorry
```

Finally, here is one last example. A metric space consists of a set equipped with a notion of distance, dist x y, mapping any pair of elements to a real number. The distance function is assumed to satisfy the following axioms:

```lean
variable {X : Type*} [MetricSpace X]
variable (x y z : X)

#check (dist_self x : dist x x = 0)
#check (dist_comm x y : dist x y = dist y x)
#check (dist_triangle x y z : dist x z ≤ dist x y + dist y z)
```


Having mastered this section, you can show that it follows from these axioms that distances are always nonnegative:

```lean
example (x y : X) : 0 ≤ dist x y := by
  sorry
```


We recommend making use of the theorem nonneg_of_mul_nonneg_left. As you may have guessed, this theorem is called dist_nonneg in Mathlib.

