---
src       : "src/plfa/part1/Quantifiers.lagda.md"
title     : "Quantifiers: Universals and existentials"
layout    : page
prev      : /Negation/
permalink : /Quantifiers/
next      : /Decidable/
---

{% raw %}<pre class="Agda"><a id="159" class="Keyword">module</a> <a id="166" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}" class="Module">plfa.part1.Quantifiers</a> <a id="189" class="Keyword">where</a>
</pre>{% endraw %}
This chapter introduces universal and existential quantification.

## Imports

{% raw %}<pre class="Agda"><a id="283" class="Keyword">import</a> <a id="290" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.html" class="Module">Relation.Binary.PropositionalEquality</a> <a id="328" class="Symbol">as</a> <a id="331" class="Module">Eq</a>
<a id="334" class="Keyword">open</a> <a id="339" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.html" class="Module">Eq</a> <a id="342" class="Keyword">using</a> <a id="348" class="Symbol">(</a><a id="349" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">_≡_</a><a id="352" class="Symbol">;</a> <a id="354" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a><a id="358" class="Symbol">)</a>
<a id="360" class="Keyword">open</a> <a id="365" class="Keyword">import</a> <a id="372" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.html" class="Module">Data.Nat</a> <a id="381" class="Keyword">using</a> <a id="387" class="Symbol">(</a><a id="388" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="389" class="Symbol">;</a> <a id="391" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a><a id="395" class="Symbol">;</a> <a id="397" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a><a id="400" class="Symbol">;</a> <a id="402" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">_+_</a><a id="405" class="Symbol">;</a> <a id="407" href="Agda.Builtin.Nat.html#501" class="Primitive Operator">_*_</a><a id="410" class="Symbol">)</a>
<a id="412" class="Keyword">open</a> <a id="417" class="Keyword">import</a> <a id="424" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html" class="Module">Relation.Nullary</a> <a id="441" class="Keyword">using</a> <a id="447" class="Symbol">(</a><a id="448" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#535" class="Function Operator">¬_</a><a id="450" class="Symbol">)</a>
<a id="452" class="Keyword">open</a> <a id="457" class="Keyword">import</a> <a id="464" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html" class="Module">Data.Product</a> <a id="477" class="Keyword">using</a> <a id="483" class="Symbol">(</a><a id="484" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1162" class="Function Operator">_×_</a><a id="487" class="Symbol">;</a> <a id="489" href="Agda.Builtin.Sigma.html#225" class="Field">proj₁</a><a id="494" class="Symbol">;</a> <a id="496" href="Agda.Builtin.Sigma.html#237" class="Field">proj₂</a><a id="501" class="Symbol">)</a> <a id="503" class="Keyword">renaming</a> <a id="512" class="Symbol">(</a><a id="513" href="Agda.Builtin.Sigma.html#209" class="InductiveConstructor Operator">_,_</a> <a id="517" class="Symbol">to</a> <a id="520" href="Agda.Builtin.Sigma.html#209" class="InductiveConstructor Operator">⟨_,_⟩</a><a id="525" class="Symbol">)</a>
<a id="527" class="Keyword">open</a> <a id="532" class="Keyword">import</a> <a id="539" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.html" class="Module">Data.Sum</a> <a id="548" class="Keyword">using</a> <a id="554" class="Symbol">(</a><a id="555" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#612" class="Datatype Operator">_⊎_</a><a id="558" class="Symbol">)</a>
<a id="560" class="Keyword">open</a> <a id="565" class="Keyword">import</a> <a id="572" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}" class="Module">plfa.part1.Isomorphism</a> <a id="595" class="Keyword">using</a> <a id="601" class="Symbol">(</a><a id="602" href="plfa.part1.Isomorphism.html#4365" class="Record Operator">_≃_</a><a id="605" class="Symbol">;</a> <a id="607" href="plfa.part1.Isomorphism.html#2684" class="Postulate">extensionality</a><a id="621" class="Symbol">)</a>
</pre>{% endraw %}

## Universals

We formalise universal quantification using the dependent function
type, which has appeared throughout this book.  For instance, in
Chapter Induction we showed addition is associative:

    +-assoc : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)

which asserts for all natural numbers `m`, `n`, and `p`
that `(m + n) + p ≡ m + (n + p)` holds.  It is a dependent
function, which given values for `m`, `n`, and `p` returns
evidence for the corresponding equation.

In general, given a variable `x` of type `A` and a proposition `B x`
which contains `x` as a free variable, the universally quantified
proposition `∀ (x : A) → B x` holds if for every term `M` of type `A`
the proposition `B M` holds.  Here `B M` stands for the proposition
`B x` with each free occurrence of `x` replaced by `M`.  Variable `x`
appears free in `B x` but bound in `∀ (x : A) → B x`.

Evidence that `∀ (x : A) → B x` holds is of the form

    λ (x : A) → N x

where `N x` is a term of type `B x`, and `N x` and `B x` both contain
a free variable `x` of type `A`.  Given a term `L` providing evidence
that `∀ (x : A) → B x` holds, and a term `M` of type `A`, the term `L
M` provides evidence that `B M` holds.  In other words, evidence that
`∀ (x : A) → B x` holds is a function that converts a term `M` of type
`A` into evidence that `B M` holds.

Put another way, if we know that `∀ (x : A) → B x` holds and that `M`
is a term of type `A` then we may conclude that `B M` holds:
{% raw %}<pre class="Agda"><a id="∀-elim"></a><a id="2099" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#2099" class="Function">∀-elim</a> <a id="2106" class="Symbol">:</a> <a id="2108" class="Symbol">∀</a> <a id="2110" class="Symbol">{</a><a id="2111" href="plfa.part1.Quantifiers.html#2111" class="Bound">A</a> <a id="2113" class="Symbol">:</a> <a id="2115" class="PrimitiveType">Set</a><a id="2118" class="Symbol">}</a> <a id="2120" class="Symbol">{</a><a id="2121" href="plfa.part1.Quantifiers.html#2121" class="Bound">B</a> <a id="2123" class="Symbol">:</a> <a id="2125" href="plfa.part1.Quantifiers.html#2111" class="Bound">A</a> <a id="2127" class="Symbol">→</a> <a id="2129" class="PrimitiveType">Set</a><a id="2132" class="Symbol">}</a>
  <a id="2136" class="Symbol">→</a> <a id="2138" class="Symbol">(</a><a id="2139" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#2139" class="Bound">L</a> <a id="2141" class="Symbol">:</a> <a id="2143" class="Symbol">∀</a> <a id="2145" class="Symbol">(</a><a id="2146" href="plfa.part1.Quantifiers.html#2146" class="Bound">x</a> <a id="2148" class="Symbol">:</a> <a id="2150" href="plfa.part1.Quantifiers.html#2111" class="Bound">A</a><a id="2151" class="Symbol">)</a> <a id="2153" class="Symbol">→</a> <a id="2155" href="plfa.part1.Quantifiers.html#2121" class="Bound">B</a> <a id="2157" href="plfa.part1.Quantifiers.html#2146" class="Bound">x</a><a id="2158" class="Symbol">)</a>
  <a id="2162" class="Symbol">→</a> <a id="2164" class="Symbol">(</a><a id="2165" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#2165" class="Bound">M</a> <a id="2167" class="Symbol">:</a> <a id="2169" href="plfa.part1.Quantifiers.html#2111" class="Bound">A</a><a id="2170" class="Symbol">)</a>
    <a id="2176" class="Comment">-----------------</a>
  <a id="2196" class="Symbol">→</a> <a id="2198" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#2121" class="Bound">B</a> <a id="2200" href="plfa.part1.Quantifiers.html#2165" class="Bound">M</a>
<a id="2202" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#2099" class="Function">∀-elim</a> <a id="2209" href="plfa.part1.Quantifiers.html#2209" class="Bound">L</a> <a id="2211" href="plfa.part1.Quantifiers.html#2211" class="Bound">M</a> <a id="2213" class="Symbol">=</a> <a id="2215" href="plfa.part1.Quantifiers.html#2209" class="Bound">L</a> <a id="2217" href="plfa.part1.Quantifiers.html#2211" class="Bound">M</a>
</pre>{% endraw %}As with `→-elim`, the rule corresponds to function application.

Functions arise as a special case of dependent functions,
where the range does not depend on a variable drawn from the domain.
When a function is viewed as evidence of implication, both its
argument and result are viewed as evidence, whereas when a dependent
function is viewed as evidence of a universal, its argument is viewed
as an element of a data type and its result is viewed as evidence of
a proposition that depends on the argument. This difference is largely
a matter of interpretation, since in Agda a value of a type and
evidence of a proposition are indistinguishable.

Dependent function types are sometimes referred to as dependent
products, because if `A` is a finite type with values `x₁ , ⋯ , xₙ`,
and if each of the types `B x₁ , ⋯ , B xₙ` has `m₁ , ⋯ , mₙ` distinct
members, then `∀ (x : A) → B x` has `m₁ * ⋯ * mₙ` members.  Indeed,
sometimes the notation `∀ (x : A) → B x` is replaced by a notation
such as `Π[ x ∈ A ] (B x)`, where `Π` stands for product.  However, we
will stick with the name dependent function, because (as we will see)
dependent product is ambiguous.


#### Exercise `∀-distrib-×` (recommended)

Show that universals distribute over conjunction:
{% raw %}<pre class="Agda"><a id="3481" class="Keyword">postulate</a>
  <a id="∀-distrib-×"></a><a id="3493" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#3493" class="Postulate">∀-distrib-×</a> <a id="3505" class="Symbol">:</a> <a id="3507" class="Symbol">∀</a> <a id="3509" class="Symbol">{</a><a id="3510" href="plfa.part1.Quantifiers.html#3510" class="Bound">A</a> <a id="3512" class="Symbol">:</a> <a id="3514" class="PrimitiveType">Set</a><a id="3517" class="Symbol">}</a> <a id="3519" class="Symbol">{</a><a id="3520" href="plfa.part1.Quantifiers.html#3520" class="Bound">B</a> <a id="3522" href="plfa.part1.Quantifiers.html#3522" class="Bound">C</a> <a id="3524" class="Symbol">:</a> <a id="3526" href="plfa.part1.Quantifiers.html#3510" class="Bound">A</a> <a id="3528" class="Symbol">→</a> <a id="3530" class="PrimitiveType">Set</a><a id="3533" class="Symbol">}</a> <a id="3535" class="Symbol">→</a>
    <a id="3541" class="Symbol">(∀</a> <a id="3544" class="Symbol">(</a><a id="3545" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#3545" class="Bound">x</a> <a id="3547" class="Symbol">:</a> <a id="3549" href="plfa.part1.Quantifiers.html#3510" class="Bound">A</a><a id="3550" class="Symbol">)</a> <a id="3552" class="Symbol">→</a> <a id="3554" href="plfa.part1.Quantifiers.html#3520" class="Bound">B</a> <a id="3556" href="plfa.part1.Quantifiers.html#3545" class="Bound">x</a> <a id="3558" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1162" class="Function Operator">×</a> <a id="3560" href="plfa.part1.Quantifiers.html#3522" class="Bound">C</a> <a id="3562" href="plfa.part1.Quantifiers.html#3545" class="Bound">x</a><a id="3563" class="Symbol">)</a> <a id="3565" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#4365" class="Record Operator">≃</a> <a id="3567" class="Symbol">(∀</a> <a id="3570" class="Symbol">(</a><a id="3571" href="plfa.part1.Quantifiers.html#3571" class="Bound">x</a> <a id="3573" class="Symbol">:</a> <a id="3575" href="plfa.part1.Quantifiers.html#3510" class="Bound">A</a><a id="3576" class="Symbol">)</a> <a id="3578" class="Symbol">→</a> <a id="3580" href="plfa.part1.Quantifiers.html#3520" class="Bound">B</a> <a id="3582" href="plfa.part1.Quantifiers.html#3571" class="Bound">x</a><a id="3583" class="Symbol">)</a> <a id="3585" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1162" class="Function Operator">×</a> <a id="3587" class="Symbol">(∀</a> <a id="3590" class="Symbol">(</a><a id="3591" href="plfa.part1.Quantifiers.html#3591" class="Bound">x</a> <a id="3593" class="Symbol">:</a> <a id="3595" href="plfa.part1.Quantifiers.html#3510" class="Bound">A</a><a id="3596" class="Symbol">)</a> <a id="3598" class="Symbol">→</a> <a id="3600" href="plfa.part1.Quantifiers.html#3522" class="Bound">C</a> <a id="3602" href="plfa.part1.Quantifiers.html#3591" class="Bound">x</a><a id="3603" class="Symbol">)</a>
</pre>{% endraw %}Compare this with the result (`→-distrib-×`) in
Chapter [Connectives]({{ site.baseurl }}/Connectives/).

#### Exercise `⊎∀-implies-∀⊎` (practice)

Show that a disjunction of universals implies a universal of disjunctions:
{% raw %}<pre class="Agda"><a id="3835" class="Keyword">postulate</a>
  <a id="⊎∀-implies-∀⊎"></a><a id="3847" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#3847" class="Postulate">⊎∀-implies-∀⊎</a> <a id="3861" class="Symbol">:</a> <a id="3863" class="Symbol">∀</a> <a id="3865" class="Symbol">{</a><a id="3866" href="plfa.part1.Quantifiers.html#3866" class="Bound">A</a> <a id="3868" class="Symbol">:</a> <a id="3870" class="PrimitiveType">Set</a><a id="3873" class="Symbol">}</a> <a id="3875" class="Symbol">{</a><a id="3876" href="plfa.part1.Quantifiers.html#3876" class="Bound">B</a> <a id="3878" href="plfa.part1.Quantifiers.html#3878" class="Bound">C</a> <a id="3880" class="Symbol">:</a> <a id="3882" href="plfa.part1.Quantifiers.html#3866" class="Bound">A</a> <a id="3884" class="Symbol">→</a> <a id="3886" class="PrimitiveType">Set</a><a id="3889" class="Symbol">}</a> <a id="3891" class="Symbol">→</a>
    <a id="3897" class="Symbol">(∀</a> <a id="3900" class="Symbol">(</a><a id="3901" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#3901" class="Bound">x</a> <a id="3903" class="Symbol">:</a> <a id="3905" href="plfa.part1.Quantifiers.html#3866" class="Bound">A</a><a id="3906" class="Symbol">)</a> <a id="3908" class="Symbol">→</a> <a id="3910" href="plfa.part1.Quantifiers.html#3876" class="Bound">B</a> <a id="3912" href="plfa.part1.Quantifiers.html#3901" class="Bound">x</a><a id="3913" class="Symbol">)</a> <a id="3915" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#612" class="Datatype Operator">⊎</a> <a id="3917" class="Symbol">(∀</a> <a id="3920" class="Symbol">(</a><a id="3921" href="plfa.part1.Quantifiers.html#3921" class="Bound">x</a> <a id="3923" class="Symbol">:</a> <a id="3925" href="plfa.part1.Quantifiers.html#3866" class="Bound">A</a><a id="3926" class="Symbol">)</a> <a id="3928" class="Symbol">→</a> <a id="3930" href="plfa.part1.Quantifiers.html#3878" class="Bound">C</a> <a id="3932" href="plfa.part1.Quantifiers.html#3921" class="Bound">x</a><a id="3933" class="Symbol">)</a>  <a id="3936" class="Symbol">→</a>  <a id="3939" class="Symbol">∀</a> <a id="3941" class="Symbol">(</a><a id="3942" href="plfa.part1.Quantifiers.html#3942" class="Bound">x</a> <a id="3944" class="Symbol">:</a> <a id="3946" href="plfa.part1.Quantifiers.html#3866" class="Bound">A</a><a id="3947" class="Symbol">)</a> <a id="3949" class="Symbol">→</a> <a id="3951" href="plfa.part1.Quantifiers.html#3876" class="Bound">B</a> <a id="3953" href="plfa.part1.Quantifiers.html#3942" class="Bound">x</a> <a id="3955" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#612" class="Datatype Operator">⊎</a> <a id="3957" href="plfa.part1.Quantifiers.html#3878" class="Bound">C</a> <a id="3959" href="plfa.part1.Quantifiers.html#3942" class="Bound">x</a>
</pre>{% endraw %}Does the converse hold? If so, prove; if not, explain why.


#### Exercise `∀-×` (practice)

Consider the following type.
{% raw %}<pre class="Agda"><a id="4091" class="Keyword">data</a> <a id="Tri"></a><a id="4096" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#4096" class="Datatype">Tri</a> <a id="4100" class="Symbol">:</a> <a id="4102" class="PrimitiveType">Set</a> <a id="4106" class="Keyword">where</a>
  <a id="Tri.aa"></a><a id="4114" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#4114" class="InductiveConstructor">aa</a> <a id="4117" class="Symbol">:</a> <a id="4119" href="plfa.part1.Quantifiers.html#4096" class="Datatype">Tri</a>
  <a id="Tri.bb"></a><a id="4125" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#4125" class="InductiveConstructor">bb</a> <a id="4128" class="Symbol">:</a> <a id="4130" href="plfa.part1.Quantifiers.html#4096" class="Datatype">Tri</a>
  <a id="Tri.cc"></a><a id="4136" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#4136" class="InductiveConstructor">cc</a> <a id="4139" class="Symbol">:</a> <a id="4141" href="plfa.part1.Quantifiers.html#4096" class="Datatype">Tri</a>
</pre>{% endraw %}Let `B` be a type indexed by `Tri`, that is `B : Tri → Set`.
Show that `∀ (x : Tri) → B x` is isomorphic to `B aa × B bb × B cc`.
Hint: you will need to postulate a version of extensionality that
works for dependent functions.


## Existentials

Given a variable `x` of type `A` and a proposition `B x` which
contains `x` as a free variable, the existentially quantified
proposition `Σ[ x ∈ A ] B x` holds if for some term `M` of type
`A` the proposition `B M` holds.  Here `B M` stands for
the proposition `B x` with each free occurrence of `x` replaced by
`M`.  Variable `x` appears free in `B x` but bound in
`Σ[ x ∈ A ] B x`.

We formalise existential quantification by declaring a suitable
inductive type:
{% raw %}<pre class="Agda"><a id="4864" class="Keyword">data</a> <a id="Σ"></a><a id="4869" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#4869" class="Datatype">Σ</a> <a id="4871" class="Symbol">(</a><a id="4872" href="plfa.part1.Quantifiers.html#4872" class="Bound">A</a> <a id="4874" class="Symbol">:</a> <a id="4876" class="PrimitiveType">Set</a><a id="4879" class="Symbol">)</a> <a id="4881" class="Symbol">(</a><a id="4882" href="plfa.part1.Quantifiers.html#4882" class="Bound">B</a> <a id="4884" class="Symbol">:</a> <a id="4886" href="plfa.part1.Quantifiers.html#4872" class="Bound">A</a> <a id="4888" class="Symbol">→</a> <a id="4890" class="PrimitiveType">Set</a><a id="4893" class="Symbol">)</a> <a id="4895" class="Symbol">:</a> <a id="4897" class="PrimitiveType">Set</a> <a id="4901" class="Keyword">where</a>
  <a id="Σ.⟨_,_⟩"></a><a id="4909" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#4909" class="InductiveConstructor Operator">⟨_,_⟩</a> <a id="4915" class="Symbol">:</a> <a id="4917" class="Symbol">(</a><a id="4918" href="plfa.part1.Quantifiers.html#4918" class="Bound">x</a> <a id="4920" class="Symbol">:</a> <a id="4922" href="plfa.part1.Quantifiers.html#4872" class="Bound">A</a><a id="4923" class="Symbol">)</a> <a id="4925" class="Symbol">→</a> <a id="4927" href="plfa.part1.Quantifiers.html#4882" class="Bound">B</a> <a id="4929" href="plfa.part1.Quantifiers.html#4918" class="Bound">x</a> <a id="4931" class="Symbol">→</a> <a id="4933" href="plfa.part1.Quantifiers.html#4869" class="Datatype">Σ</a> <a id="4935" href="plfa.part1.Quantifiers.html#4872" class="Bound">A</a> <a id="4937" href="plfa.part1.Quantifiers.html#4882" class="Bound">B</a>
</pre>{% endraw %}We define a convenient syntax for existentials as follows:
{% raw %}<pre class="Agda"><a id="Σ-syntax"></a><a id="5006" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#5006" class="Function">Σ-syntax</a> <a id="5015" class="Symbol">=</a> <a id="5017" href="plfa.part1.Quantifiers.html#4869" class="Datatype">Σ</a>
<a id="5019" class="Keyword">infix</a> <a id="5025" class="Number">2</a> <a id="5027" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#5006" class="Function">Σ-syntax</a>
<a id="5036" class="Keyword">syntax</a> <a id="5043" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#5006" class="Function">Σ-syntax</a> <a id="5052" class="Bound">A</a> <a id="5054" class="Symbol">(λ</a> <a id="5057" class="Bound">x</a> <a id="5059" class="Symbol">→</a> <a id="5061" class="Bound">B</a><a id="5062" class="Symbol">)</a> <a id="5064" class="Symbol">=</a> <a id="5066" class="Function">Σ[</a> <a id="5069" class="Bound">x</a> <a id="5071" class="Function">∈</a> <a id="5073" class="Bound">A</a> <a id="5075" class="Function">]</a> <a id="5077" class="Bound">B</a>
</pre>{% endraw %}This is our first use of a syntax declaration, which specifies that
the term on the left may be written with the syntax on the right.
The special syntax is available only when the identifier
`Σ-syntax` is imported.

Evidence that `Σ[ x ∈ A ] B x` holds is of the form
`⟨ M , N ⟩` where `M` is a term of type `A`, and `N` is evidence
that `B M` holds.

Equivalently, we could also declare existentials as a record type:
{% raw %}<pre class="Agda"><a id="5506" class="Keyword">record</a> <a id="Σ′"></a><a id="5513" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#5513" class="Record">Σ′</a> <a id="5516" class="Symbol">(</a><a id="5517" href="plfa.part1.Quantifiers.html#5517" class="Bound">A</a> <a id="5519" class="Symbol">:</a> <a id="5521" class="PrimitiveType">Set</a><a id="5524" class="Symbol">)</a> <a id="5526" class="Symbol">(</a><a id="5527" href="plfa.part1.Quantifiers.html#5527" class="Bound">B</a> <a id="5529" class="Symbol">:</a> <a id="5531" href="plfa.part1.Quantifiers.html#5517" class="Bound">A</a> <a id="5533" class="Symbol">→</a> <a id="5535" class="PrimitiveType">Set</a><a id="5538" class="Symbol">)</a> <a id="5540" class="Symbol">:</a> <a id="5542" class="PrimitiveType">Set</a> <a id="5546" class="Keyword">where</a>
  <a id="5554" class="Keyword">field</a>
    <a id="Σ′.proj₁′"></a><a id="5564" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#5564" class="Field">proj₁′</a> <a id="5571" class="Symbol">:</a> <a id="5573" href="plfa.part1.Quantifiers.html#5517" class="Bound">A</a>
    <a id="Σ′.proj₂′"></a><a id="5579" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#5579" class="Field">proj₂′</a> <a id="5586" class="Symbol">:</a> <a id="5588" href="plfa.part1.Quantifiers.html#5527" class="Bound">B</a> <a id="5590" href="plfa.part1.Quantifiers.html#5564" class="Field">proj₁′</a>
</pre>{% endraw %}Here record construction

    record
      { proj₁′ = M
      ; proj₂′ = N
      }

corresponds to the term

    ⟨ M , N ⟩

where `M` is a term of type `A` and `N` is a term of type `B M`.

Products arise as a special case of existentials, where the second
component does not depend on a variable drawn from the first
component.  When a product is viewed as evidence of a conjunction,
both of its components are viewed as evidence, whereas when it is
viewed as evidence of an existential, the first component is viewed as
an element of a datatype and the second component is viewed as
evidence of a proposition that depends on the first component.  This
difference is largely a matter of interpretation, since in Agda a value
of a type and evidence of a proposition are indistinguishable.

Existentials are sometimes referred to as dependent sums,
because if `A` is a finite type with values `x₁ , ⋯ , xₙ`, and if
each of the types `B x₁ , ⋯ B xₙ` has `m₁ , ⋯ , mₙ` distinct members,
then `Σ[ x ∈ A ] B x` has `m₁ + ⋯ + mₙ` members, which explains the
choice of notation for existentials, since `Σ` stands for sum.

Existentials are sometimes referred to as dependent products, since
products arise as a special case.  However, that choice of names is
doubly confusing, since universals also have a claim to the name dependent
product and since existentials also have a claim to the name dependent sum.

A common notation for existentials is `∃` (analogous to `∀` for universals).
We follow the convention of the Agda standard library, and reserve this
notation for the case where the domain of the bound variable is left implicit:
{% raw %}<pre class="Agda"><a id="∃"></a><a id="7237" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#7237" class="Function">∃</a> <a id="7239" class="Symbol">:</a> <a id="7241" class="Symbol">∀</a> <a id="7243" class="Symbol">{</a><a id="7244" href="plfa.part1.Quantifiers.html#7244" class="Bound">A</a> <a id="7246" class="Symbol">:</a> <a id="7248" class="PrimitiveType">Set</a><a id="7251" class="Symbol">}</a> <a id="7253" class="Symbol">(</a><a id="7254" href="plfa.part1.Quantifiers.html#7254" class="Bound">B</a> <a id="7256" class="Symbol">:</a> <a id="7258" href="plfa.part1.Quantifiers.html#7244" class="Bound">A</a> <a id="7260" class="Symbol">→</a> <a id="7262" class="PrimitiveType">Set</a><a id="7265" class="Symbol">)</a> <a id="7267" class="Symbol">→</a> <a id="7269" class="PrimitiveType">Set</a>
<a id="7273" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#7237" class="Function">∃</a> <a id="7275" class="Symbol">{</a><a id="7276" href="plfa.part1.Quantifiers.html#7276" class="Bound">A</a><a id="7277" class="Symbol">}</a> <a id="7279" href="plfa.part1.Quantifiers.html#7279" class="Bound">B</a> <a id="7281" class="Symbol">=</a> <a id="7283" href="plfa.part1.Quantifiers.html#4869" class="Datatype">Σ</a> <a id="7285" href="plfa.part1.Quantifiers.html#7276" class="Bound">A</a> <a id="7287" href="plfa.part1.Quantifiers.html#7279" class="Bound">B</a>

<a id="∃-syntax"></a><a id="7290" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#7290" class="Function">∃-syntax</a> <a id="7299" class="Symbol">=</a> <a id="7301" href="plfa.part1.Quantifiers.html#7237" class="Function">∃</a>
<a id="7303" class="Keyword">syntax</a> <a id="7310" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#7290" class="Function">∃-syntax</a> <a id="7319" class="Symbol">(λ</a> <a id="7322" class="Bound">x</a> <a id="7324" class="Symbol">→</a> <a id="7326" class="Bound">B</a><a id="7327" class="Symbol">)</a> <a id="7329" class="Symbol">=</a> <a id="7331" class="Function">∃[</a> <a id="7334" class="Bound">x</a> <a id="7336" class="Function">]</a> <a id="7338" class="Bound">B</a>
</pre>{% endraw %}The special syntax is available only when the identifier `∃-syntax` is imported.
We will tend to use this syntax, since it is shorter and more familiar.

Given evidence that `∀ x → B x → C` holds, where `C` does not contain
`x` as a free variable, and given evidence that `∃[ x ] B x` holds, we
may conclude that `C` holds:
{% raw %}<pre class="Agda"><a id="∃-elim"></a><a id="7672" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#7672" class="Function">∃-elim</a> <a id="7679" class="Symbol">:</a> <a id="7681" class="Symbol">∀</a> <a id="7683" class="Symbol">{</a><a id="7684" href="plfa.part1.Quantifiers.html#7684" class="Bound">A</a> <a id="7686" class="Symbol">:</a> <a id="7688" class="PrimitiveType">Set</a><a id="7691" class="Symbol">}</a> <a id="7693" class="Symbol">{</a><a id="7694" href="plfa.part1.Quantifiers.html#7694" class="Bound">B</a> <a id="7696" class="Symbol">:</a> <a id="7698" href="plfa.part1.Quantifiers.html#7684" class="Bound">A</a> <a id="7700" class="Symbol">→</a> <a id="7702" class="PrimitiveType">Set</a><a id="7705" class="Symbol">}</a> <a id="7707" class="Symbol">{</a><a id="7708" href="plfa.part1.Quantifiers.html#7708" class="Bound">C</a> <a id="7710" class="Symbol">:</a> <a id="7712" class="PrimitiveType">Set</a><a id="7715" class="Symbol">}</a>
  <a id="7719" class="Symbol">→</a> <a id="7721" class="Symbol">(∀</a> <a id="7724" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#7724" class="Bound">x</a> <a id="7726" class="Symbol">→</a> <a id="7728" href="plfa.part1.Quantifiers.html#7694" class="Bound">B</a> <a id="7730" href="plfa.part1.Quantifiers.html#7724" class="Bound">x</a> <a id="7732" class="Symbol">→</a> <a id="7734" href="plfa.part1.Quantifiers.html#7708" class="Bound">C</a><a id="7735" class="Symbol">)</a>
  <a id="7739" class="Symbol">→</a> <a id="7741" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#7290" class="Function">∃[</a> <a id="7744" href="plfa.part1.Quantifiers.html#7744" class="Bound">x</a> <a id="7746" href="plfa.part1.Quantifiers.html#7290" class="Function">]</a> <a id="7748" href="plfa.part1.Quantifiers.html#7694" class="Bound">B</a> <a id="7750" href="plfa.part1.Quantifiers.html#7744" class="Bound">x</a>
    <a id="7756" class="Comment">---------------</a>
  <a id="7774" class="Symbol">→</a> <a id="7776" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#7708" class="Bound">C</a>
<a id="7778" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#7672" class="Function">∃-elim</a> <a id="7785" href="plfa.part1.Quantifiers.html#7785" class="Bound">f</a> <a id="7787" href="plfa.part1.Quantifiers.html#4909" class="InductiveConstructor Operator">⟨</a> <a id="7789" href="plfa.part1.Quantifiers.html#7789" class="Bound">x</a> <a id="7791" href="plfa.part1.Quantifiers.html#4909" class="InductiveConstructor Operator">,</a> <a id="7793" href="plfa.part1.Quantifiers.html#7793" class="Bound">y</a> <a id="7795" href="plfa.part1.Quantifiers.html#4909" class="InductiveConstructor Operator">⟩</a> <a id="7797" class="Symbol">=</a> <a id="7799" href="plfa.part1.Quantifiers.html#7785" class="Bound">f</a> <a id="7801" href="plfa.part1.Quantifiers.html#7789" class="Bound">x</a> <a id="7803" href="plfa.part1.Quantifiers.html#7793" class="Bound">y</a>
</pre>{% endraw %}In other words, if we know for every `x` of type `A` that `B x`
implies `C`, and we know for some `x` of type `A` that `B x` holds,
then we may conclude that `C` holds.  This is because we may
instantiate that proof that `∀ x → B x → C` to any value `x` of type
`A` and any `y` of type `B x`, and exactly such values are provided by
the evidence for `∃[ x ] B x`.

Indeed, the converse also holds, and the two together form an isomorphism:
{% raw %}<pre class="Agda"><a id="∀∃-currying"></a><a id="8253" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#8253" class="Function">∀∃-currying</a> <a id="8265" class="Symbol">:</a> <a id="8267" class="Symbol">∀</a> <a id="8269" class="Symbol">{</a><a id="8270" href="plfa.part1.Quantifiers.html#8270" class="Bound">A</a> <a id="8272" class="Symbol">:</a> <a id="8274" class="PrimitiveType">Set</a><a id="8277" class="Symbol">}</a> <a id="8279" class="Symbol">{</a><a id="8280" href="plfa.part1.Quantifiers.html#8280" class="Bound">B</a> <a id="8282" class="Symbol">:</a> <a id="8284" href="plfa.part1.Quantifiers.html#8270" class="Bound">A</a> <a id="8286" class="Symbol">→</a> <a id="8288" class="PrimitiveType">Set</a><a id="8291" class="Symbol">}</a> <a id="8293" class="Symbol">{</a><a id="8294" href="plfa.part1.Quantifiers.html#8294" class="Bound">C</a> <a id="8296" class="Symbol">:</a> <a id="8298" class="PrimitiveType">Set</a><a id="8301" class="Symbol">}</a>
  <a id="8305" class="Symbol">→</a> <a id="8307" class="Symbol">(∀</a> <a id="8310" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#8310" class="Bound">x</a> <a id="8312" class="Symbol">→</a> <a id="8314" href="plfa.part1.Quantifiers.html#8280" class="Bound">B</a> <a id="8316" href="plfa.part1.Quantifiers.html#8310" class="Bound">x</a> <a id="8318" class="Symbol">→</a> <a id="8320" href="plfa.part1.Quantifiers.html#8294" class="Bound">C</a><a id="8321" class="Symbol">)</a> <a id="8323" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#4365" class="Record Operator">≃</a> <a id="8325" class="Symbol">(</a><a id="8326" href="plfa.part1.Quantifiers.html#7290" class="Function">∃[</a> <a id="8329" href="plfa.part1.Quantifiers.html#8329" class="Bound">x</a> <a id="8331" href="plfa.part1.Quantifiers.html#7290" class="Function">]</a> <a id="8333" href="plfa.part1.Quantifiers.html#8280" class="Bound">B</a> <a id="8335" href="plfa.part1.Quantifiers.html#8329" class="Bound">x</a> <a id="8337" class="Symbol">→</a> <a id="8339" href="plfa.part1.Quantifiers.html#8294" class="Bound">C</a><a id="8340" class="Symbol">)</a>
<a id="8342" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#8253" class="Function">∀∃-currying</a> <a id="8354" class="Symbol">=</a>
  <a id="8358" class="Keyword">record</a>
    <a id="8369" class="Symbol">{</a> <a id="8371" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#4405" class="Field">to</a>      <a id="8379" class="Symbol">=</a>  <a id="8382" class="Symbol">λ{</a> <a id="8385" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#8385" class="Bound">f</a> <a id="8387" class="Symbol">→</a> <a id="8389" class="Symbol">λ{</a> <a id="8392" href="plfa.part1.Quantifiers.html#4909" class="InductiveConstructor Operator">⟨</a> <a id="8394" href="plfa.part1.Quantifiers.html#8394" class="Bound">x</a> <a id="8396" href="plfa.part1.Quantifiers.html#4909" class="InductiveConstructor Operator">,</a> <a id="8398" href="plfa.part1.Quantifiers.html#8398" class="Bound">y</a> <a id="8400" href="plfa.part1.Quantifiers.html#4909" class="InductiveConstructor Operator">⟩</a> <a id="8402" class="Symbol">→</a> <a id="8404" href="plfa.part1.Quantifiers.html#8385" class="Bound">f</a> <a id="8406" href="plfa.part1.Quantifiers.html#8394" class="Bound">x</a> <a id="8408" href="plfa.part1.Quantifiers.html#8398" class="Bound">y</a> <a id="8410" class="Symbol">}}</a>
    <a id="8417" class="Symbol">;</a> <a id="8419" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#4422" class="Field">from</a>    <a id="8427" class="Symbol">=</a>  <a id="8430" class="Symbol">λ{</a> <a id="8433" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#8433" class="Bound">g</a> <a id="8435" class="Symbol">→</a> <a id="8437" class="Symbol">λ{</a> <a id="8440" href="plfa.part1.Quantifiers.html#8440" class="Bound">x</a> <a id="8442" class="Symbol">→</a> <a id="8444" class="Symbol">λ{</a> <a id="8447" href="plfa.part1.Quantifiers.html#8447" class="Bound">y</a> <a id="8449" class="Symbol">→</a> <a id="8451" href="plfa.part1.Quantifiers.html#8433" class="Bound">g</a> <a id="8453" href="plfa.part1.Quantifiers.html#4909" class="InductiveConstructor Operator">⟨</a> <a id="8455" href="plfa.part1.Quantifiers.html#8440" class="Bound">x</a> <a id="8457" href="plfa.part1.Quantifiers.html#4909" class="InductiveConstructor Operator">,</a> <a id="8459" href="plfa.part1.Quantifiers.html#8447" class="Bound">y</a> <a id="8461" href="plfa.part1.Quantifiers.html#4909" class="InductiveConstructor Operator">⟩</a> <a id="8463" class="Symbol">}}}</a>
    <a id="8471" class="Symbol">;</a> <a id="8473" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#4439" class="Field">from∘to</a> <a id="8481" class="Symbol">=</a>  <a id="8484" class="Symbol">λ{</a> <a id="8487" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#8487" class="Bound">f</a> <a id="8489" class="Symbol">→</a> <a id="8491" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="8496" class="Symbol">}</a>
    <a id="8502" class="Symbol">;</a> <a id="8504" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#4481" class="Field">to∘from</a> <a id="8512" class="Symbol">=</a>  <a id="8515" class="Symbol">λ{</a> <a id="8518" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#8518" class="Bound">g</a> <a id="8520" class="Symbol">→</a> <a id="8522" href="plfa.part1.Isomorphism.html#2684" class="Postulate">extensionality</a> <a id="8537" class="Symbol">λ{</a> <a id="8540" href="plfa.part1.Quantifiers.html#4909" class="InductiveConstructor Operator">⟨</a> <a id="8542" href="plfa.part1.Quantifiers.html#8542" class="Bound">x</a> <a id="8544" href="plfa.part1.Quantifiers.html#4909" class="InductiveConstructor Operator">,</a> <a id="8546" href="plfa.part1.Quantifiers.html#8546" class="Bound">y</a> <a id="8548" href="plfa.part1.Quantifiers.html#4909" class="InductiveConstructor Operator">⟩</a> <a id="8550" class="Symbol">→</a> <a id="8552" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="8557" class="Symbol">}}</a>
    <a id="8564" class="Symbol">}</a>
</pre>{% endraw %}The result can be viewed as a generalisation of currying.  Indeed, the code to
establish the isomorphism is identical to what we wrote when discussing
[implication]({{ site.baseurl }}/Connectives/#implication).

#### Exercise `∃-distrib-⊎` (recommended)

Show that existentials distribute over disjunction:
{% raw %}<pre class="Agda"><a id="8881" class="Keyword">postulate</a>
  <a id="∃-distrib-⊎"></a><a id="8893" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#8893" class="Postulate">∃-distrib-⊎</a> <a id="8905" class="Symbol">:</a> <a id="8907" class="Symbol">∀</a> <a id="8909" class="Symbol">{</a><a id="8910" href="plfa.part1.Quantifiers.html#8910" class="Bound">A</a> <a id="8912" class="Symbol">:</a> <a id="8914" class="PrimitiveType">Set</a><a id="8917" class="Symbol">}</a> <a id="8919" class="Symbol">{</a><a id="8920" href="plfa.part1.Quantifiers.html#8920" class="Bound">B</a> <a id="8922" href="plfa.part1.Quantifiers.html#8922" class="Bound">C</a> <a id="8924" class="Symbol">:</a> <a id="8926" href="plfa.part1.Quantifiers.html#8910" class="Bound">A</a> <a id="8928" class="Symbol">→</a> <a id="8930" class="PrimitiveType">Set</a><a id="8933" class="Symbol">}</a> <a id="8935" class="Symbol">→</a>
    <a id="8941" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#7290" class="Function">∃[</a> <a id="8944" href="plfa.part1.Quantifiers.html#8944" class="Bound">x</a> <a id="8946" href="plfa.part1.Quantifiers.html#7290" class="Function">]</a> <a id="8948" class="Symbol">(</a><a id="8949" href="plfa.part1.Quantifiers.html#8920" class="Bound">B</a> <a id="8951" href="plfa.part1.Quantifiers.html#8944" class="Bound">x</a> <a id="8953" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#612" class="Datatype Operator">⊎</a> <a id="8955" href="plfa.part1.Quantifiers.html#8922" class="Bound">C</a> <a id="8957" href="plfa.part1.Quantifiers.html#8944" class="Bound">x</a><a id="8958" class="Symbol">)</a> <a id="8960" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#4365" class="Record Operator">≃</a> <a id="8962" class="Symbol">(</a><a id="8963" href="plfa.part1.Quantifiers.html#7290" class="Function">∃[</a> <a id="8966" href="plfa.part1.Quantifiers.html#8966" class="Bound">x</a> <a id="8968" href="plfa.part1.Quantifiers.html#7290" class="Function">]</a> <a id="8970" href="plfa.part1.Quantifiers.html#8920" class="Bound">B</a> <a id="8972" href="plfa.part1.Quantifiers.html#8966" class="Bound">x</a><a id="8973" class="Symbol">)</a> <a id="8975" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#612" class="Datatype Operator">⊎</a> <a id="8977" class="Symbol">(</a><a id="8978" href="plfa.part1.Quantifiers.html#7290" class="Function">∃[</a> <a id="8981" href="plfa.part1.Quantifiers.html#8981" class="Bound">x</a> <a id="8983" href="plfa.part1.Quantifiers.html#7290" class="Function">]</a> <a id="8985" href="plfa.part1.Quantifiers.html#8922" class="Bound">C</a> <a id="8987" href="plfa.part1.Quantifiers.html#8981" class="Bound">x</a><a id="8988" class="Symbol">)</a>
</pre>{% endraw %}
#### Exercise `∃×-implies-×∃` (practice)

Show that an existential of conjunctions implies a conjunction of existentials:
{% raw %}<pre class="Agda"><a id="9121" class="Keyword">postulate</a>
  <a id="∃×-implies-×∃"></a><a id="9133" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#9133" class="Postulate">∃×-implies-×∃</a> <a id="9147" class="Symbol">:</a> <a id="9149" class="Symbol">∀</a> <a id="9151" class="Symbol">{</a><a id="9152" href="plfa.part1.Quantifiers.html#9152" class="Bound">A</a> <a id="9154" class="Symbol">:</a> <a id="9156" class="PrimitiveType">Set</a><a id="9159" class="Symbol">}</a> <a id="9161" class="Symbol">{</a><a id="9162" href="plfa.part1.Quantifiers.html#9162" class="Bound">B</a> <a id="9164" href="plfa.part1.Quantifiers.html#9164" class="Bound">C</a> <a id="9166" class="Symbol">:</a> <a id="9168" href="plfa.part1.Quantifiers.html#9152" class="Bound">A</a> <a id="9170" class="Symbol">→</a> <a id="9172" class="PrimitiveType">Set</a><a id="9175" class="Symbol">}</a> <a id="9177" class="Symbol">→</a>
    <a id="9183" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#7290" class="Function">∃[</a> <a id="9186" href="plfa.part1.Quantifiers.html#9186" class="Bound">x</a> <a id="9188" href="plfa.part1.Quantifiers.html#7290" class="Function">]</a> <a id="9190" class="Symbol">(</a><a id="9191" href="plfa.part1.Quantifiers.html#9162" class="Bound">B</a> <a id="9193" href="plfa.part1.Quantifiers.html#9186" class="Bound">x</a> <a id="9195" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1162" class="Function Operator">×</a> <a id="9197" href="plfa.part1.Quantifiers.html#9164" class="Bound">C</a> <a id="9199" href="plfa.part1.Quantifiers.html#9186" class="Bound">x</a><a id="9200" class="Symbol">)</a> <a id="9202" class="Symbol">→</a> <a id="9204" class="Symbol">(</a><a id="9205" href="plfa.part1.Quantifiers.html#7290" class="Function">∃[</a> <a id="9208" href="plfa.part1.Quantifiers.html#9208" class="Bound">x</a> <a id="9210" href="plfa.part1.Quantifiers.html#7290" class="Function">]</a> <a id="9212" href="plfa.part1.Quantifiers.html#9162" class="Bound">B</a> <a id="9214" href="plfa.part1.Quantifiers.html#9208" class="Bound">x</a><a id="9215" class="Symbol">)</a> <a id="9217" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1162" class="Function Operator">×</a> <a id="9219" class="Symbol">(</a><a id="9220" href="plfa.part1.Quantifiers.html#7290" class="Function">∃[</a> <a id="9223" href="plfa.part1.Quantifiers.html#9223" class="Bound">x</a> <a id="9225" href="plfa.part1.Quantifiers.html#7290" class="Function">]</a> <a id="9227" href="plfa.part1.Quantifiers.html#9164" class="Bound">C</a> <a id="9229" href="plfa.part1.Quantifiers.html#9223" class="Bound">x</a><a id="9230" class="Symbol">)</a>
</pre>{% endraw %}Does the converse hold? If so, prove; if not, explain why.

#### Exercise `∃-⊎` (practice)

Let `Tri` and `B` be as in Exercise `∀-×`.
Show that `∃[ x ] B x` is isomorphic to `B aa ⊎ B bb ⊎ B cc`.


## An existential example

Recall the definitions of `even` and `odd` from
Chapter [Relations]({{ site.baseurl }}/Relations/):
{% raw %}<pre class="Agda"><a id="9566" class="Keyword">data</a> <a id="even"></a><a id="9571" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#9571" class="Datatype">even</a> <a id="9576" class="Symbol">:</a> <a id="9578" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a> <a id="9580" class="Symbol">→</a> <a id="9582" class="PrimitiveType">Set</a>
<a id="9586" class="Keyword">data</a> <a id="odd"></a><a id="9591" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#9591" class="Datatype">odd</a>  <a id="9596" class="Symbol">:</a> <a id="9598" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a> <a id="9600" class="Symbol">→</a> <a id="9602" class="PrimitiveType">Set</a>

<a id="9607" class="Keyword">data</a> <a id="9612" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#9571" class="Datatype">even</a> <a id="9617" class="Keyword">where</a>

  <a id="even.even-zero"></a><a id="9626" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#9626" class="InductiveConstructor">even-zero</a> <a id="9636" class="Symbol">:</a> <a id="9638" href="plfa.part1.Quantifiers.html#9571" class="Datatype">even</a> <a id="9643" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a>

  <a id="even.even-suc"></a><a id="9651" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#9651" class="InductiveConstructor">even-suc</a> <a id="9660" class="Symbol">:</a> <a id="9662" class="Symbol">∀</a> <a id="9664" class="Symbol">{</a><a id="9665" href="plfa.part1.Quantifiers.html#9665" class="Bound">n</a> <a id="9667" class="Symbol">:</a> <a id="9669" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="9670" class="Symbol">}</a>
    <a id="9676" class="Symbol">→</a> <a id="9678" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#9591" class="Datatype">odd</a> <a id="9682" href="plfa.part1.Quantifiers.html#9665" class="Bound">n</a>
      <a id="9690" class="Comment">------------</a>
    <a id="9707" class="Symbol">→</a> <a id="9709" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#9571" class="Datatype">even</a> <a id="9714" class="Symbol">(</a><a id="9715" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="9719" href="plfa.part1.Quantifiers.html#9665" class="Bound">n</a><a id="9720" class="Symbol">)</a>

<a id="9723" class="Keyword">data</a> <a id="9728" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#9591" class="Datatype">odd</a> <a id="9732" class="Keyword">where</a>
  <a id="odd.odd-suc"></a><a id="9740" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#9740" class="InductiveConstructor">odd-suc</a> <a id="9748" class="Symbol">:</a> <a id="9750" class="Symbol">∀</a> <a id="9752" class="Symbol">{</a><a id="9753" href="plfa.part1.Quantifiers.html#9753" class="Bound">n</a> <a id="9755" class="Symbol">:</a> <a id="9757" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="9758" class="Symbol">}</a>
    <a id="9764" class="Symbol">→</a> <a id="9766" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#9571" class="Datatype">even</a> <a id="9771" href="plfa.part1.Quantifiers.html#9753" class="Bound">n</a>
      <a id="9779" class="Comment">-----------</a>
    <a id="9795" class="Symbol">→</a> <a id="9797" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#9591" class="Datatype">odd</a> <a id="9801" class="Symbol">(</a><a id="9802" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="9806" href="plfa.part1.Quantifiers.html#9753" class="Bound">n</a><a id="9807" class="Symbol">)</a>
</pre>{% endraw %}A number is even if it is zero or the successor of an odd number, and
odd if it is the successor of an even number.

We will show that a number is even if and only if it is twice some
other number, and odd if and only if it is one more than twice
some other number.  In other words, we will show:

`even n`   iff   `∃[ m ] (    m * 2 ≡ n)`

`odd  n`   iff   `∃[ m ] (1 + m * 2 ≡ n)`

By convention, one tends to write constant factors first and to put
the constant term in a sum last. Here we've reversed each of those
conventions, because doing so eases the proof.

Here is the proof in the forward direction:
{% raw %}<pre class="Agda"><a id="even-∃"></a><a id="10428" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#10428" class="Function">even-∃</a> <a id="10435" class="Symbol">:</a> <a id="10437" class="Symbol">∀</a> <a id="10439" class="Symbol">{</a><a id="10440" href="plfa.part1.Quantifiers.html#10440" class="Bound">n</a> <a id="10442" class="Symbol">:</a> <a id="10444" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="10445" class="Symbol">}</a> <a id="10447" class="Symbol">→</a> <a id="10449" href="plfa.part1.Quantifiers.html#9571" class="Datatype">even</a> <a id="10454" href="plfa.part1.Quantifiers.html#10440" class="Bound">n</a> <a id="10456" class="Symbol">→</a> <a id="10458" href="plfa.part1.Quantifiers.html#7290" class="Function">∃[</a> <a id="10461" href="plfa.part1.Quantifiers.html#10461" class="Bound">m</a> <a id="10463" href="plfa.part1.Quantifiers.html#7290" class="Function">]</a> <a id="10465" class="Symbol">(</a>    <a id="10470" href="plfa.part1.Quantifiers.html#10461" class="Bound">m</a> <a id="10472" href="Agda.Builtin.Nat.html#501" class="Primitive Operator">*</a> <a id="10474" class="Number">2</a> <a id="10476" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="10478" href="plfa.part1.Quantifiers.html#10440" class="Bound">n</a><a id="10479" class="Symbol">)</a>
<a id="odd-∃"></a><a id="10481" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#10481" class="Function">odd-∃</a>  <a id="10488" class="Symbol">:</a> <a id="10490" class="Symbol">∀</a> <a id="10492" class="Symbol">{</a><a id="10493" href="plfa.part1.Quantifiers.html#10493" class="Bound">n</a> <a id="10495" class="Symbol">:</a> <a id="10497" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="10498" class="Symbol">}</a> <a id="10500" class="Symbol">→</a>  <a id="10503" href="plfa.part1.Quantifiers.html#9591" class="Datatype">odd</a> <a id="10507" href="plfa.part1.Quantifiers.html#10493" class="Bound">n</a> <a id="10509" class="Symbol">→</a> <a id="10511" href="plfa.part1.Quantifiers.html#7290" class="Function">∃[</a> <a id="10514" href="plfa.part1.Quantifiers.html#10514" class="Bound">m</a> <a id="10516" href="plfa.part1.Quantifiers.html#7290" class="Function">]</a> <a id="10518" class="Symbol">(</a><a id="10519" class="Number">1</a> <a id="10521" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="10523" href="plfa.part1.Quantifiers.html#10514" class="Bound">m</a> <a id="10525" href="Agda.Builtin.Nat.html#501" class="Primitive Operator">*</a> <a id="10527" class="Number">2</a> <a id="10529" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="10531" href="plfa.part1.Quantifiers.html#10493" class="Bound">n</a><a id="10532" class="Symbol">)</a>

<a id="10535" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#10428" class="Function">even-∃</a> <a id="10542" href="plfa.part1.Quantifiers.html#9626" class="InductiveConstructor">even-zero</a>                       <a id="10574" class="Symbol">=</a>  <a id="10577" href="plfa.part1.Quantifiers.html#4909" class="InductiveConstructor Operator">⟨</a> <a id="10579" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a> <a id="10584" href="plfa.part1.Quantifiers.html#4909" class="InductiveConstructor Operator">,</a> <a id="10586" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="10591" href="plfa.part1.Quantifiers.html#4909" class="InductiveConstructor Operator">⟩</a>
<a id="10593" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#10428" class="Function">even-∃</a> <a id="10600" class="Symbol">(</a><a id="10601" href="plfa.part1.Quantifiers.html#9651" class="InductiveConstructor">even-suc</a> <a id="10610" href="plfa.part1.Quantifiers.html#10610" class="Bound">o</a><a id="10611" class="Symbol">)</a> <a id="10613" class="Keyword">with</a> <a id="10618" href="plfa.part1.Quantifiers.html#10481" class="Function">odd-∃</a> <a id="10624" href="plfa.part1.Quantifiers.html#10610" class="Bound">o</a>
<a id="10626" class="Symbol">...</a>                    <a id="10649" class="Symbol">|</a> <a id="10651" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#4909" class="InductiveConstructor Operator">⟨</a> <a id="10653" href="plfa.part1.Quantifiers.html#10653" class="Bound">m</a> <a id="10655" href="plfa.part1.Quantifiers.html#4909" class="InductiveConstructor Operator">,</a> <a id="10657" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="10662" href="plfa.part1.Quantifiers.html#4909" class="InductiveConstructor Operator">⟩</a>  <a id="10665" class="Symbol">=</a>  <a id="10668" href="plfa.part1.Quantifiers.html#4909" class="InductiveConstructor Operator">⟨</a> <a id="10670" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="10674" href="plfa.part1.Quantifiers.html#10653" class="Bound">m</a> <a id="10676" href="plfa.part1.Quantifiers.html#4909" class="InductiveConstructor Operator">,</a> <a id="10678" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="10683" href="plfa.part1.Quantifiers.html#4909" class="InductiveConstructor Operator">⟩</a>

<a id="10686" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#10481" class="Function">odd-∃</a>  <a id="10693" class="Symbol">(</a><a id="10694" href="plfa.part1.Quantifiers.html#9740" class="InductiveConstructor">odd-suc</a> <a id="10702" href="plfa.part1.Quantifiers.html#10702" class="Bound">e</a><a id="10703" class="Symbol">)</a>  <a id="10706" class="Keyword">with</a> <a id="10711" href="plfa.part1.Quantifiers.html#10428" class="Function">even-∃</a> <a id="10718" href="plfa.part1.Quantifiers.html#10702" class="Bound">e</a>
<a id="10720" class="Symbol">...</a>                    <a id="10743" class="Symbol">|</a> <a id="10745" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#4909" class="InductiveConstructor Operator">⟨</a> <a id="10747" href="plfa.part1.Quantifiers.html#10747" class="Bound">m</a> <a id="10749" href="plfa.part1.Quantifiers.html#4909" class="InductiveConstructor Operator">,</a> <a id="10751" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="10756" href="plfa.part1.Quantifiers.html#4909" class="InductiveConstructor Operator">⟩</a>  <a id="10759" class="Symbol">=</a>  <a id="10762" href="plfa.part1.Quantifiers.html#4909" class="InductiveConstructor Operator">⟨</a> <a id="10764" href="plfa.part1.Quantifiers.html#10747" class="Bound">m</a> <a id="10766" href="plfa.part1.Quantifiers.html#4909" class="InductiveConstructor Operator">,</a> <a id="10768" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="10773" href="plfa.part1.Quantifiers.html#4909" class="InductiveConstructor Operator">⟩</a>
</pre>{% endraw %}We define two mutually recursive functions. Given
evidence that `n` is even or odd, we return a
number `m` and evidence that `m * 2 ≡ n` or `1 + m * 2 ≡ n`.
We induct over the evidence that `n` is even or odd:

* If the number is even because it is zero, then we return a pair
consisting of zero and the evidence that twice zero is zero.

* If the number is even because it is one more than an odd number,
then we apply the induction hypothesis to give a number `m` and
evidence that `1 + m * 2 ≡ n`. We return a pair consisting of `suc m`
and evidence that `suc m * 2 ≡ suc n`, which is immediate after
substituting for `n`.

* If the number is odd because it is the successor of an even number,
then we apply the induction hypothesis to give a number `m` and
evidence that `m * 2 ≡ n`. We return a pair consisting of `suc m` and
evidence that `1 + m * 2 ≡ suc n`, which is immediate after
substituting for `n`.

This completes the proof in the forward direction.

Here is the proof in the reverse direction:
{% raw %}<pre class="Agda"><a id="∃-even"></a><a id="11793" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#11793" class="Function">∃-even</a> <a id="11800" class="Symbol">:</a> <a id="11802" class="Symbol">∀</a> <a id="11804" class="Symbol">{</a><a id="11805" href="plfa.part1.Quantifiers.html#11805" class="Bound">n</a> <a id="11807" class="Symbol">:</a> <a id="11809" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="11810" class="Symbol">}</a> <a id="11812" class="Symbol">→</a> <a id="11814" href="plfa.part1.Quantifiers.html#7290" class="Function">∃[</a> <a id="11817" href="plfa.part1.Quantifiers.html#11817" class="Bound">m</a> <a id="11819" href="plfa.part1.Quantifiers.html#7290" class="Function">]</a> <a id="11821" class="Symbol">(</a>    <a id="11826" href="plfa.part1.Quantifiers.html#11817" class="Bound">m</a> <a id="11828" href="Agda.Builtin.Nat.html#501" class="Primitive Operator">*</a> <a id="11830" class="Number">2</a> <a id="11832" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="11834" href="plfa.part1.Quantifiers.html#11805" class="Bound">n</a><a id="11835" class="Symbol">)</a> <a id="11837" class="Symbol">→</a> <a id="11839" href="plfa.part1.Quantifiers.html#9571" class="Datatype">even</a> <a id="11844" href="plfa.part1.Quantifiers.html#11805" class="Bound">n</a>
<a id="∃-odd"></a><a id="11846" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#11846" class="Function">∃-odd</a>  <a id="11853" class="Symbol">:</a> <a id="11855" class="Symbol">∀</a> <a id="11857" class="Symbol">{</a><a id="11858" href="plfa.part1.Quantifiers.html#11858" class="Bound">n</a> <a id="11860" class="Symbol">:</a> <a id="11862" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="11863" class="Symbol">}</a> <a id="11865" class="Symbol">→</a> <a id="11867" href="plfa.part1.Quantifiers.html#7290" class="Function">∃[</a> <a id="11870" href="plfa.part1.Quantifiers.html#11870" class="Bound">m</a> <a id="11872" href="plfa.part1.Quantifiers.html#7290" class="Function">]</a> <a id="11874" class="Symbol">(</a><a id="11875" class="Number">1</a> <a id="11877" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="11879" href="plfa.part1.Quantifiers.html#11870" class="Bound">m</a> <a id="11881" href="Agda.Builtin.Nat.html#501" class="Primitive Operator">*</a> <a id="11883" class="Number">2</a> <a id="11885" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="11887" href="plfa.part1.Quantifiers.html#11858" class="Bound">n</a><a id="11888" class="Symbol">)</a> <a id="11890" class="Symbol">→</a>  <a id="11893" href="plfa.part1.Quantifiers.html#9591" class="Datatype">odd</a> <a id="11897" href="plfa.part1.Quantifiers.html#11858" class="Bound">n</a>

<a id="11900" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#11793" class="Function">∃-even</a> <a id="11907" href="plfa.part1.Quantifiers.html#4909" class="InductiveConstructor Operator">⟨</a>  <a id="11910" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a> <a id="11915" href="plfa.part1.Quantifiers.html#4909" class="InductiveConstructor Operator">,</a> <a id="11917" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="11922" href="plfa.part1.Quantifiers.html#4909" class="InductiveConstructor Operator">⟩</a>  <a id="11925" class="Symbol">=</a>  <a id="11928" href="plfa.part1.Quantifiers.html#9626" class="InductiveConstructor">even-zero</a>
<a id="11938" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#11793" class="Function">∃-even</a> <a id="11945" href="plfa.part1.Quantifiers.html#4909" class="InductiveConstructor Operator">⟨</a> <a id="11947" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="11951" href="plfa.part1.Quantifiers.html#11951" class="Bound">m</a> <a id="11953" href="plfa.part1.Quantifiers.html#4909" class="InductiveConstructor Operator">,</a> <a id="11955" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="11960" href="plfa.part1.Quantifiers.html#4909" class="InductiveConstructor Operator">⟩</a>  <a id="11963" class="Symbol">=</a>  <a id="11966" href="plfa.part1.Quantifiers.html#9651" class="InductiveConstructor">even-suc</a> <a id="11975" class="Symbol">(</a><a id="11976" href="plfa.part1.Quantifiers.html#11846" class="Function">∃-odd</a> <a id="11982" href="plfa.part1.Quantifiers.html#4909" class="InductiveConstructor Operator">⟨</a> <a id="11984" href="plfa.part1.Quantifiers.html#11951" class="Bound">m</a> <a id="11986" href="plfa.part1.Quantifiers.html#4909" class="InductiveConstructor Operator">,</a> <a id="11988" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="11993" href="plfa.part1.Quantifiers.html#4909" class="InductiveConstructor Operator">⟩</a><a id="11994" class="Symbol">)</a>

<a id="11997" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#11846" class="Function">∃-odd</a>  <a id="12004" href="plfa.part1.Quantifiers.html#4909" class="InductiveConstructor Operator">⟨</a>     <a id="12010" href="plfa.part1.Quantifiers.html#12010" class="Bound">m</a> <a id="12012" href="plfa.part1.Quantifiers.html#4909" class="InductiveConstructor Operator">,</a> <a id="12014" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="12019" href="plfa.part1.Quantifiers.html#4909" class="InductiveConstructor Operator">⟩</a>  <a id="12022" class="Symbol">=</a>  <a id="12025" href="plfa.part1.Quantifiers.html#9740" class="InductiveConstructor">odd-suc</a> <a id="12033" class="Symbol">(</a><a id="12034" href="plfa.part1.Quantifiers.html#11793" class="Function">∃-even</a> <a id="12041" href="plfa.part1.Quantifiers.html#4909" class="InductiveConstructor Operator">⟨</a> <a id="12043" href="plfa.part1.Quantifiers.html#12010" class="Bound">m</a> <a id="12045" href="plfa.part1.Quantifiers.html#4909" class="InductiveConstructor Operator">,</a> <a id="12047" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="12052" href="plfa.part1.Quantifiers.html#4909" class="InductiveConstructor Operator">⟩</a><a id="12053" class="Symbol">)</a>
</pre>{% endraw %}Given a number that is twice some other number we must show it is
even, and a number that is one more than twice some other number we
must show it is odd.  We induct over the evidence of the existential,
and in the even case consider the two possibilities for the number
that is doubled:

- In the even case for `zero`, we must show `zero * 2` is even, which
follows by `even-zero`.

- In the even case for `suc n`, we must show `suc m * 2` is even.  The
inductive hypothesis tells us that `1 + m * 2` is odd, from which the
desired result follows by `even-suc`.

- In the odd case, we must show `1 + m * 2` is odd.  The inductive
hypothesis tell us that `m * 2` is even, from which the desired result
follows by `odd-suc`.

This completes the proof in the backward direction.

#### Exercise `∃-even-odd` (practice)

How do the proofs become more difficult if we replace `m * 2` and `1 + m * 2`
by `2 * m` and `2 * m + 1`?  Rewrite the proofs of `∃-even` and `∃-odd` when
restated in this way.

{% raw %}<pre class="Agda"><a id="13058" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}
#### Exercise `∃-+-≤` (practice)

Show that `y ≤ z` holds if and only if there exists a `x` such that
`x + y ≡ z`.

{% raw %}<pre class="Agda"><a id="13206" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}

## Existentials, Universals, and Negation

Negation of an existential is isomorphic to the universal
of a negation.  Considering that existentials are generalised
disjunction and universals are generalised conjunction, this
result is analogous to the one which tells us that negation
of a disjunction is isomorphic to a conjunction of negations:
{% raw %}<pre class="Agda"><a id="¬∃≃∀¬"></a><a id="13585" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#13585" class="Function">¬∃≃∀¬</a> <a id="13591" class="Symbol">:</a> <a id="13593" class="Symbol">∀</a> <a id="13595" class="Symbol">{</a><a id="13596" href="plfa.part1.Quantifiers.html#13596" class="Bound">A</a> <a id="13598" class="Symbol">:</a> <a id="13600" class="PrimitiveType">Set</a><a id="13603" class="Symbol">}</a> <a id="13605" class="Symbol">{</a><a id="13606" href="plfa.part1.Quantifiers.html#13606" class="Bound">B</a> <a id="13608" class="Symbol">:</a> <a id="13610" href="plfa.part1.Quantifiers.html#13596" class="Bound">A</a> <a id="13612" class="Symbol">→</a> <a id="13614" class="PrimitiveType">Set</a><a id="13617" class="Symbol">}</a>
  <a id="13621" class="Symbol">→</a> <a id="13623" class="Symbol">(</a><a id="13624" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#535" class="Function Operator">¬</a> <a id="13626" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#7290" class="Function">∃[</a> <a id="13629" href="plfa.part1.Quantifiers.html#13629" class="Bound">x</a> <a id="13631" href="plfa.part1.Quantifiers.html#7290" class="Function">]</a> <a id="13633" href="plfa.part1.Quantifiers.html#13606" class="Bound">B</a> <a id="13635" href="plfa.part1.Quantifiers.html#13629" class="Bound">x</a><a id="13636" class="Symbol">)</a> <a id="13638" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#4365" class="Record Operator">≃</a> <a id="13640" class="Symbol">∀</a> <a id="13642" href="plfa.part1.Quantifiers.html#13642" class="Bound">x</a> <a id="13644" class="Symbol">→</a> <a id="13646" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#535" class="Function Operator">¬</a> <a id="13648" href="plfa.part1.Quantifiers.html#13606" class="Bound">B</a> <a id="13650" href="plfa.part1.Quantifiers.html#13642" class="Bound">x</a>
<a id="13652" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#13585" class="Function">¬∃≃∀¬</a> <a id="13658" class="Symbol">=</a>
  <a id="13662" class="Keyword">record</a>
    <a id="13673" class="Symbol">{</a> <a id="13675" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#4405" class="Field">to</a>      <a id="13683" class="Symbol">=</a>  <a id="13686" class="Symbol">λ{</a> <a id="13689" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#13689" class="Bound">¬∃xy</a> <a id="13694" href="plfa.part1.Quantifiers.html#13694" class="Bound">x</a> <a id="13696" href="plfa.part1.Quantifiers.html#13696" class="Bound">y</a> <a id="13698" class="Symbol">→</a> <a id="13700" href="plfa.part1.Quantifiers.html#13689" class="Bound">¬∃xy</a> <a id="13705" href="plfa.part1.Quantifiers.html#4909" class="InductiveConstructor Operator">⟨</a> <a id="13707" href="plfa.part1.Quantifiers.html#13694" class="Bound">x</a> <a id="13709" href="plfa.part1.Quantifiers.html#4909" class="InductiveConstructor Operator">,</a> <a id="13711" href="plfa.part1.Quantifiers.html#13696" class="Bound">y</a> <a id="13713" href="plfa.part1.Quantifiers.html#4909" class="InductiveConstructor Operator">⟩</a> <a id="13715" class="Symbol">}</a>
    <a id="13721" class="Symbol">;</a> <a id="13723" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#4422" class="Field">from</a>    <a id="13731" class="Symbol">=</a>  <a id="13734" class="Symbol">λ{</a> <a id="13737" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#13737" class="Bound">∀¬xy</a> <a id="13742" href="plfa.part1.Quantifiers.html#4909" class="InductiveConstructor Operator">⟨</a> <a id="13744" href="plfa.part1.Quantifiers.html#13744" class="Bound">x</a> <a id="13746" href="plfa.part1.Quantifiers.html#4909" class="InductiveConstructor Operator">,</a> <a id="13748" href="plfa.part1.Quantifiers.html#13748" class="Bound">y</a> <a id="13750" href="plfa.part1.Quantifiers.html#4909" class="InductiveConstructor Operator">⟩</a> <a id="13752" class="Symbol">→</a> <a id="13754" href="plfa.part1.Quantifiers.html#13737" class="Bound">∀¬xy</a> <a id="13759" href="plfa.part1.Quantifiers.html#13744" class="Bound">x</a> <a id="13761" href="plfa.part1.Quantifiers.html#13748" class="Bound">y</a> <a id="13763" class="Symbol">}</a>
    <a id="13769" class="Symbol">;</a> <a id="13771" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#4439" class="Field">from∘to</a> <a id="13779" class="Symbol">=</a>  <a id="13782" class="Symbol">λ{</a> <a id="13785" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#13785" class="Bound">¬∃xy</a> <a id="13790" class="Symbol">→</a> <a id="13792" href="plfa.part1.Isomorphism.html#2684" class="Postulate">extensionality</a> <a id="13807" class="Symbol">λ{</a> <a id="13810" href="plfa.part1.Quantifiers.html#4909" class="InductiveConstructor Operator">⟨</a> <a id="13812" href="plfa.part1.Quantifiers.html#13812" class="Bound">x</a> <a id="13814" href="plfa.part1.Quantifiers.html#4909" class="InductiveConstructor Operator">,</a> <a id="13816" href="plfa.part1.Quantifiers.html#13816" class="Bound">y</a> <a id="13818" href="plfa.part1.Quantifiers.html#4909" class="InductiveConstructor Operator">⟩</a> <a id="13820" class="Symbol">→</a> <a id="13822" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="13827" class="Symbol">}</a> <a id="13829" class="Symbol">}</a>
    <a id="13835" class="Symbol">;</a> <a id="13837" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#4481" class="Field">to∘from</a> <a id="13845" class="Symbol">=</a>  <a id="13848" class="Symbol">λ{</a> <a id="13851" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#13851" class="Bound">∀¬xy</a> <a id="13856" class="Symbol">→</a> <a id="13858" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="13863" class="Symbol">}</a>
    <a id="13869" class="Symbol">}</a>
</pre>{% endraw %}In the `to` direction, we are given a value `¬∃xy` of type
`¬ ∃[ x ] B x`, and need to show that given a value
`x` that `¬ B x` follows, in other words, from
a value `y` of type `B x` we can derive false.  Combining
`x` and `y` gives us a value `⟨ x , y ⟩` of type `∃[ x ] B x`,
and applying `¬∃xy` to that yields a contradiction.

In the `from` direction, we are given a value `∀¬xy` of type
`∀ x → ¬ B x`, and need to show that from a value `⟨ x , y ⟩`
of type `∃[ x ] B x` we can derive false.  Applying `∀¬xy`
to `x` gives a value of type `¬ B x`, and applying that to `y` yields
a contradiction.

The two inverse proofs are straightforward, where one direction
requires extensionality.


#### Exercise `∃¬-implies-¬∀` (recommended)

Show that existential of a negation implies negation of a universal:
{% raw %}<pre class="Agda"><a id="14686" class="Keyword">postulate</a>
  <a id="∃¬-implies-¬∀"></a><a id="14698" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#14698" class="Postulate">∃¬-implies-¬∀</a> <a id="14712" class="Symbol">:</a> <a id="14714" class="Symbol">∀</a> <a id="14716" class="Symbol">{</a><a id="14717" href="plfa.part1.Quantifiers.html#14717" class="Bound">A</a> <a id="14719" class="Symbol">:</a> <a id="14721" class="PrimitiveType">Set</a><a id="14724" class="Symbol">}</a> <a id="14726" class="Symbol">{</a><a id="14727" href="plfa.part1.Quantifiers.html#14727" class="Bound">B</a> <a id="14729" class="Symbol">:</a> <a id="14731" href="plfa.part1.Quantifiers.html#14717" class="Bound">A</a> <a id="14733" class="Symbol">→</a> <a id="14735" class="PrimitiveType">Set</a><a id="14738" class="Symbol">}</a>
    <a id="14744" class="Symbol">→</a> <a id="14746" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#7290" class="Function">∃[</a> <a id="14749" href="plfa.part1.Quantifiers.html#14749" class="Bound">x</a> <a id="14751" href="plfa.part1.Quantifiers.html#7290" class="Function">]</a> <a id="14753" class="Symbol">(</a><a id="14754" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#535" class="Function Operator">¬</a> <a id="14756" href="plfa.part1.Quantifiers.html#14727" class="Bound">B</a> <a id="14758" href="plfa.part1.Quantifiers.html#14749" class="Bound">x</a><a id="14759" class="Symbol">)</a>
      <a id="14767" class="Comment">--------------</a>
    <a id="14786" class="Symbol">→</a> <a id="14788" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#535" class="Function Operator">¬</a> <a id="14790" class="Symbol">(∀</a> <a id="14793" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#14793" class="Bound">x</a> <a id="14795" class="Symbol">→</a> <a id="14797" href="plfa.part1.Quantifiers.html#14727" class="Bound">B</a> <a id="14799" href="plfa.part1.Quantifiers.html#14793" class="Bound">x</a><a id="14800" class="Symbol">)</a>
</pre>{% endraw %}Does the converse hold? If so, prove; if not, explain why.


#### Exercise `Bin-isomorphism` (stretch) {#Bin-isomorphism}

Recall that Exercises
[Bin]({{ site.baseurl }}/Naturals/#Bin),
[Bin-laws]({{ site.baseurl }}/Induction/#Bin-laws), and
[Bin-predicates]({{ site.baseurl }}/Relations/#Bin-predicates)
define a datatype `Bin` of bitstrings representing natural numbers,
and asks you to define the following functions and predicates:

    to   : ℕ → Bin
    from : Bin → ℕ
    Can  : Bin → Set

And to establish the following properties:

    from (to n) ≡ n

    ----------
    Can (to n)

    Can b
    ---------------
    to (from b) ≡ b

Using the above, establish that there is an isomorphism between `ℕ` and
`∃[ b ](Can b)`.

We recommend proving the following lemmas which show that, for a given
binary number `b`, there is only one proof of `One b` and similarly
for `Can b`.

    ≡One : ∀{b : Bin} (o o' : One b) → o ≡ o'
    
    ≡Can : ∀{b : Bin} (cb : Can b) (cb' : Can b) → cb ≡ cb'

Many of the alternatives for proving `to∘from` turn out to be tricky.
However, the proof can be straightforward if you use the following lemma,
which is a corollary of `≡Can`.

    proj₁≡→Can≡ : {cb cb′ : ∃[ b ](Can b)} → proj₁ cb ≡ proj₁ cb′ → cb ≡ cb′

{% raw %}<pre class="Agda"><a id="16064" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}

## Standard library

Definitions similar to those in this chapter can be found in the standard library:
{% raw %}<pre class="Agda"><a id="16201" class="Keyword">import</a> <a id="16208" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html" class="Module">Data.Product</a> <a id="16221" class="Keyword">using</a> <a id="16227" class="Symbol">(</a><a id="16228" href="Agda.Builtin.Sigma.html#139" class="Record">Σ</a><a id="16229" class="Symbol">;</a> <a id="16231" href="Agda.Builtin.Sigma.html#209" class="InductiveConstructor Operator">_,_</a><a id="16234" class="Symbol">;</a> <a id="16236" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1364" class="Function">∃</a><a id="16237" class="Symbol">;</a> <a id="16239" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#911" class="Function">Σ-syntax</a><a id="16247" class="Symbol">;</a> <a id="16249" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1783" class="Function">∃-syntax</a><a id="16257" class="Symbol">)</a>
</pre>{% endraw %}

## Unicode

This chapter uses the following unicode:

    Π  U+03A0  GREEK CAPITAL LETTER PI (\Pi)
    Σ  U+03A3  GREEK CAPITAL LETTER SIGMA (\Sigma)
    ∃  U+2203  THERE EXISTS (\ex, \exists)
