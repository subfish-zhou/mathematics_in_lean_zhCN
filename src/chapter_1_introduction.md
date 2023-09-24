# 概述

简单来说, Lean是一种构建复杂表达式的工具, 建立在被称作依值类型论(dependent type theory)的形式语言上.

每一个表达式拥有一个类型, 你可以使用`#check`命令来检查它们. 一些数学对象表达式属于ℕ或ℕ → ℕ类型. 例如:

```lean
-- 译者注：此处需要导入
-- import Mathlib.Data.Nat.Basic
-- 注意导入包的语句都需要放在文件开头
#check 2 + 2

def f (x : ℕ) :=
  x + 3

#check f
```

一些数学命题表达式属于Prop类型, 例如:

```lean
#check 2 + 2 = 4

def FermatLastTheorem :=
  ∀ x y z n : ℕ, n > 2 ∧ x * y * z ≠ 0 → x ^ n + y ^ n ≠ z ^ n

#check FermatLastTheorem
```

还有一些表达式属于类型P, 然后P属于类型Prop. 这类表达式是命题P的证明. 例如

```lean
theorem easy : 2 + 2 = 4 :=
  rfl

#check easy

theorem hard : FermatLastTheorem :=
  sorry

#check hard
```

如果你设法构造了fermat_last_theorem类型的表达式, 并且Lean接受它作为该类型的项, 那么你已经做了一些非常了不起的事情. (`sorry`是作弊, lean会提醒你在作弊但是会继续执行)

这本书是对相关教程[《Lean定理证明》](https://subfish-zhou.github.io/theorem_proving_in_lean4_zh_CN/)[(theorm proving in lean)](https://lean-lang.org/theorem_proving_in_lean4/)的补充, 那份教程更全面地介绍了Lean的基本逻辑框架和核心语法. 《Lean定理证明》适用于那些喜欢在使用新机器之前从头到尾阅读用户手册的人. 如果你是那种喜欢点击开始按钮, 然后弄清楚如何激活各种特性的人, 那么从这里开始, 并在必要时参考《Lean定理证明》会更有意义. 

《Lean中的数学》与《Lean定理证明》的另一个区别是, 此处更加强调证明策略(tactic)的使用. 假设我们正在尝试构建复杂的表达式, Lean提供了两种方法: 我们可以写下表达式本身(即适当的文本描述), 或者我们可以向Lean提供关于如何构建它们的说明. 例如, 下面的表达式证明了如果n是偶数, 那么m * n也是偶数:

```lean
-- 译者注：
-- 这里even需要导入
-- import Mathlib.algebra.parity
-- 或者定义
-- def even (n : nat) : Prop := ∃ (k : nat) , n = 2 * k
-- 二者择一，不可同用
-- 欲知导入何种library，可以在mathlib上搜索

example : ∀ m n : Nat, Even n → Even (m * n) := 
  fun m n ⟨k, (hk : n = k + k)⟩ ↦
  have hmn : m * n = m * k + m * k := by rw [hk, mul_add]
  show ∃ l, m * n = l + l from ⟨_, hmn⟩
```

证明项也可以写到一行之内:

```lean
example : ∀ m n : Nat, Even n → Even (m * n) :=
fun m n ⟨k, hk⟩ ↦ ⟨m * k, by rw [hk, mul_add]⟩
```

策略式的证明是下面这样:

```lean
import tactic --导入策略
example : ∀ m n : nat, even n → even (m * n) := by
  -- 设m和n是自然数, 然后假设n=2*k
  rintros m n ⟨k, hk⟩
  -- 需要证明m*n 是自然数的两倍, 现在说明它是两倍的m*k
  use m * k
  -- 代入n
  rw [hk]
  -- 现在就很明显了
  ring
```

当你在VScode里面敲下每行证明时, Lean会在单独的窗口里显示证明状态, 告诉你已经获得了何种事实以及接下来你面对的目标. 你可以移动光标位置, Lean会根据你的光标位置输出对应点处的状态. 在本例中,第一行引入了`m`和`n`(只要你觉得好看你也可以换别的名字), 然后把假设`even n`分解为`k`和`n = 2 * k`. 第二行声明了我们即将通过`m * n = 2 * (m * k)`说明`m * n`是偶数. 下一行使用`rewrite`策略把目标中的`n`换为`2 * k`, 最终使用`ring`策略解决了结尾目标`m * (2 * k) = 2 * (m * k)`.

通过小步骤和增量反馈构建证明的能力是非常强大的, 因此策略证明通常比证明项更容易更快. 两者之间没有明显的区别: 策略证明可以插入证明项中, 正如我们在`by rw [hk, mul_left_comm]`中所做的那样. 反过来在策略证明中插入短的证明项也是有用的, 本教程的重点在于策略证明.

上面的策略证明也可以被缩进一行里:

```lean
example : ∀ m n : Nat, Even n → Even (m * n) := by
  rintro m n ⟨k, hk⟩; use m * k; rw [hk]; ring
```

这里我们使用了一些小步前进策略. 但Lean也提供大量的自动化策略, 并合理证明更长的计算和更大的推理步骤. 例如, 我们可以使用特定的规则调用Lean的简化器来简化关于奇偶性的陈述, 从而自动证明我们的定理. 

```lean
example : ∀ m n : Nat, Even n → Even (m * n) := by
  intros; simp [*, parity_simps]
```

《Lean定理证明》与本教程间的另一个巨大区别是, 前者只依赖于核心Lean及其内置策略, 而本教程则构建在Lean的强大且不断增长的库--Mathlib之上. 因此, 我们可以向你展示如何使用库中的一些数学对象和定理, 以及一些非常有用的策略. 这本书不会对Mathlib进行完整的概述; [社区](https://leanprover-community.github.io/)网页包含大量的文档. 相反, 我们的目标是向你介绍形式化基础上的思维方式, 以便你可以轻松地浏览Mathlib并自己查找内容. 

交互式定理证明有时是令人沮丧的, 并且学习曲线是陡峭的. 但是Lean社区非常欢迎新人,在那里社区成员可以24小时在[Lean Zulip聊天群](https://leanprover.zulipchat.com/)中回答问题. 我们希望在那里见到你, 并且毫无疑问, 很快你也将能够回答这些问题, 并为Mathlib的发展做出贡献. 

所以这是你的任务, 如果你选择接受它: 潜心学习, 多加练习,带着问题来Zulip, 并祝你玩得开心. 但要预先警告: 交互式定理证明将给你一些挑战，从而你将以全新的方式思考数学和数学推理. 你的生活可能从此不同. 

*Acknowledgments*. We are grateful to Gabriel Ebner for setting up the infrastructure for running this tutorial in VS Code. We are also grateful for help from Bryan Gin-ge Chen, Johan Commelin, Julian Külshammer, and Guilherme Silva. Our work has been partially supported by the Hoskinson Center for Formal Mathematics.

感谢rujia liu老师审校译本,感谢中文类型论社区Infinity Type Café的群友们对译本的大力支持. 