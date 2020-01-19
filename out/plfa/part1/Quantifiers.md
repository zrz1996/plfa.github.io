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
<a id="452" class="Keyword">open</a> <a id="457" class="Keyword">import</a> <a id="464" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html" class="Module">Data.Product</a> <a id="477" class="Keyword">using</a> <a id="483" class="Symbol">(</a><a id="484" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1162" class="Function Operator">_×_</a><a id="487" class="Symbol">;</a> <a id="489" href="Agda.Builtin.Sigma.html#225" class="Field">proj₁</a><a id="494" class="Symbol">)</a> <a id="496" class="Keyword">renaming</a> <a id="505" class="Symbol">(</a><a id="506" href="Agda.Builtin.Sigma.html#209" class="InductiveConstructor Operator">_,_</a> <a id="510" class="Symbol">to</a> <a id="513" href="Agda.Builtin.Sigma.html#209" class="InductiveConstructor Operator">⟨_,_⟩</a><a id="518" class="Symbol">)</a>
<a id="520" class="Keyword">open</a> <a id="525" class="Keyword">import</a> <a id="532" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.html" class="Module">Data.Sum</a> <a id="541" class="Keyword">using</a> <a id="547" class="Symbol">(</a><a id="548" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#612" class="Datatype Operator">_⊎_</a><a id="551" class="Symbol">)</a>
<a id="553" class="Keyword">open</a> <a id="558" class="Keyword">import</a> <a id="565" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}" class="Module">plfa.part1.Isomorphism</a> <a id="588" class="Keyword">using</a> <a id="594" class="Symbol">(</a><a id="595" href="plfa.part1.Isomorphism.html#4365" class="Record Operator">_≃_</a><a id="598" class="Symbol">;</a> <a id="600" href="plfa.part1.Isomorphism.html#2684" class="Postulate">extensionality</a><a id="614" class="Symbol">)</a>
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
{% raw %}<pre class="Agda"><a id="∀-elim"></a><a id="2092" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#2092" class="Function">∀-elim</a> <a id="2099" class="Symbol">:</a> <a id="2101" class="Symbol">∀</a> <a id="2103" class="Symbol">{</a><a id="2104" href="plfa.part1.Quantifiers.html#2104" class="Bound">A</a> <a id="2106" class="Symbol">:</a> <a id="2108" class="PrimitiveType">Set</a><a id="2111" class="Symbol">}</a> <a id="2113" class="Symbol">{</a><a id="2114" href="plfa.part1.Quantifiers.html#2114" class="Bound">B</a> <a id="2116" class="Symbol">:</a> <a id="2118" href="plfa.part1.Quantifiers.html#2104" class="Bound">A</a> <a id="2120" class="Symbol">→</a> <a id="2122" class="PrimitiveType">Set</a><a id="2125" class="Symbol">}</a>
  <a id="2129" class="Symbol">→</a> <a id="2131" class="Symbol">(</a><a id="2132" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#2132" class="Bound">L</a> <a id="2134" class="Symbol">:</a> <a id="2136" class="Symbol">∀</a> <a id="2138" class="Symbol">(</a><a id="2139" href="plfa.part1.Quantifiers.html#2139" class="Bound">x</a> <a id="2141" class="Symbol">:</a> <a id="2143" href="plfa.part1.Quantifiers.html#2104" class="Bound">A</a><a id="2144" class="Symbol">)</a> <a id="2146" class="Symbol">→</a> <a id="2148" href="plfa.part1.Quantifiers.html#2114" class="Bound">B</a> <a id="2150" href="plfa.part1.Quantifiers.html#2139" class="Bound">x</a><a id="2151" class="Symbol">)</a>
  <a id="2155" class="Symbol">→</a> <a id="2157" class="Symbol">(</a><a id="2158" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#2158" class="Bound">M</a> <a id="2160" class="Symbol">:</a> <a id="2162" href="plfa.part1.Quantifiers.html#2104" class="Bound">A</a><a id="2163" class="Symbol">)</a>
    <a id="2169" class="Comment">-----------------</a>
  <a id="2189" class="Symbol">→</a> <a id="2191" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#2114" class="Bound">B</a> <a id="2193" href="plfa.part1.Quantifiers.html#2158" class="Bound">M</a>
<a id="2195" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#2092" class="Function">∀-elim</a> <a id="2202" href="plfa.part1.Quantifiers.html#2202" class="Bound">L</a> <a id="2204" href="plfa.part1.Quantifiers.html#2204" class="Bound">M</a> <a id="2206" class="Symbol">=</a> <a id="2208" href="plfa.part1.Quantifiers.html#2202" class="Bound">L</a> <a id="2210" href="plfa.part1.Quantifiers.html#2204" class="Bound">M</a>
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
{% raw %}<pre class="Agda"><a id="3474" class="Keyword">postulate</a>
  <a id="∀-distrib-×"></a><a id="3486" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#3486" class="Postulate">∀-distrib-×</a> <a id="3498" class="Symbol">:</a> <a id="3500" class="Symbol">∀</a> <a id="3502" class="Symbol">{</a><a id="3503" href="plfa.part1.Quantifiers.html#3503" class="Bound">A</a> <a id="3505" class="Symbol">:</a> <a id="3507" class="PrimitiveType">Set</a><a id="3510" class="Symbol">}</a> <a id="3512" class="Symbol">{</a><a id="3513" href="plfa.part1.Quantifiers.html#3513" class="Bound">B</a> <a id="3515" href="plfa.part1.Quantifiers.html#3515" class="Bound">C</a> <a id="3517" class="Symbol">:</a> <a id="3519" href="plfa.part1.Quantifiers.html#3503" class="Bound">A</a> <a id="3521" class="Symbol">→</a> <a id="3523" class="PrimitiveType">Set</a><a id="3526" class="Symbol">}</a> <a id="3528" class="Symbol">→</a>
    <a id="3534" class="Symbol">(∀</a> <a id="3537" class="Symbol">(</a><a id="3538" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#3538" class="Bound">x</a> <a id="3540" class="Symbol">:</a> <a id="3542" href="plfa.part1.Quantifiers.html#3503" class="Bound">A</a><a id="3543" class="Symbol">)</a> <a id="3545" class="Symbol">→</a> <a id="3547" href="plfa.part1.Quantifiers.html#3513" class="Bound">B</a> <a id="3549" href="plfa.part1.Quantifiers.html#3538" class="Bound">x</a> <a id="3551" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1162" class="Function Operator">×</a> <a id="3553" href="plfa.part1.Quantifiers.html#3515" class="Bound">C</a> <a id="3555" href="plfa.part1.Quantifiers.html#3538" class="Bound">x</a><a id="3556" class="Symbol">)</a> <a id="3558" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#4365" class="Record Operator">≃</a> <a id="3560" class="Symbol">(∀</a> <a id="3563" class="Symbol">(</a><a id="3564" href="plfa.part1.Quantifiers.html#3564" class="Bound">x</a> <a id="3566" class="Symbol">:</a> <a id="3568" href="plfa.part1.Quantifiers.html#3503" class="Bound">A</a><a id="3569" class="Symbol">)</a> <a id="3571" class="Symbol">→</a> <a id="3573" href="plfa.part1.Quantifiers.html#3513" class="Bound">B</a> <a id="3575" href="plfa.part1.Quantifiers.html#3564" class="Bound">x</a><a id="3576" class="Symbol">)</a> <a id="3578" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1162" class="Function Operator">×</a> <a id="3580" class="Symbol">(∀</a> <a id="3583" class="Symbol">(</a><a id="3584" href="plfa.part1.Quantifiers.html#3584" class="Bound">x</a> <a id="3586" class="Symbol">:</a> <a id="3588" href="plfa.part1.Quantifiers.html#3503" class="Bound">A</a><a id="3589" class="Symbol">)</a> <a id="3591" class="Symbol">→</a> <a id="3593" href="plfa.part1.Quantifiers.html#3515" class="Bound">C</a> <a id="3595" href="plfa.part1.Quantifiers.html#3584" class="Bound">x</a><a id="3596" class="Symbol">)</a>
</pre>{% endraw %}Compare this with the result (`→-distrib-×`) in
Chapter [Connectives]({{ site.baseurl }}/Connectives/).

#### Exercise `⊎∀-implies-∀⊎` (practice)

Show that a disjunction of universals implies a universal of disjunctions:
{% raw %}<pre class="Agda"><a id="3828" class="Keyword">postulate</a>
  <a id="⊎∀-implies-∀⊎"></a><a id="3840" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#3840" class="Postulate">⊎∀-implies-∀⊎</a> <a id="3854" class="Symbol">:</a> <a id="3856" class="Symbol">∀</a> <a id="3858" class="Symbol">{</a><a id="3859" href="plfa.part1.Quantifiers.html#3859" class="Bound">A</a> <a id="3861" class="Symbol">:</a> <a id="3863" class="PrimitiveType">Set</a><a id="3866" class="Symbol">}</a> <a id="3868" class="Symbol">{</a><a id="3869" href="plfa.part1.Quantifiers.html#3869" class="Bound">B</a> <a id="3871" href="plfa.part1.Quantifiers.html#3871" class="Bound">C</a> <a id="3873" class="Symbol">:</a> <a id="3875" href="plfa.part1.Quantifiers.html#3859" class="Bound">A</a> <a id="3877" class="Symbol">→</a> <a id="3879" class="PrimitiveType">Set</a><a id="3882" class="Symbol">}</a> <a id="3884" class="Symbol">→</a>
    <a id="3890" class="Symbol">(∀</a> <a id="3893" class="Symbol">(</a><a id="3894" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#3894" class="Bound">x</a> <a id="3896" class="Symbol">:</a> <a id="3898" href="plfa.part1.Quantifiers.html#3859" class="Bound">A</a><a id="3899" class="Symbol">)</a> <a id="3901" class="Symbol">→</a> <a id="3903" href="plfa.part1.Quantifiers.html#3869" class="Bound">B</a> <a id="3905" href="plfa.part1.Quantifiers.html#3894" class="Bound">x</a><a id="3906" class="Symbol">)</a> <a id="3908" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#612" class="Datatype Operator">⊎</a> <a id="3910" class="Symbol">(∀</a> <a id="3913" class="Symbol">(</a><a id="3914" href="plfa.part1.Quantifiers.html#3914" class="Bound">x</a> <a id="3916" class="Symbol">:</a> <a id="3918" href="plfa.part1.Quantifiers.html#3859" class="Bound">A</a><a id="3919" class="Symbol">)</a> <a id="3921" class="Symbol">→</a> <a id="3923" href="plfa.part1.Quantifiers.html#3871" class="Bound">C</a> <a id="3925" href="plfa.part1.Quantifiers.html#3914" class="Bound">x</a><a id="3926" class="Symbol">)</a>  <a id="3929" class="Symbol">→</a>  <a id="3932" class="Symbol">∀</a> <a id="3934" class="Symbol">(</a><a id="3935" href="plfa.part1.Quantifiers.html#3935" class="Bound">x</a> <a id="3937" class="Symbol">:</a> <a id="3939" href="plfa.part1.Quantifiers.html#3859" class="Bound">A</a><a id="3940" class="Symbol">)</a> <a id="3942" class="Symbol">→</a> <a id="3944" href="plfa.part1.Quantifiers.html#3869" class="Bound">B</a> <a id="3946" href="plfa.part1.Quantifiers.html#3935" class="Bound">x</a> <a id="3948" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#612" class="Datatype Operator">⊎</a> <a id="3950" href="plfa.part1.Quantifiers.html#3871" class="Bound">C</a> <a id="3952" href="plfa.part1.Quantifiers.html#3935" class="Bound">x</a>
</pre>{% endraw %}Does the converse hold? If so, prove; if not, explain why.


#### Exercise `∀-×` (practice)

Consider the following type.
{% raw %}<pre class="Agda"><a id="4084" class="Keyword">data</a> <a id="Tri"></a><a id="4089" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#4089" class="Datatype">Tri</a> <a id="4093" class="Symbol">:</a> <a id="4095" class="PrimitiveType">Set</a> <a id="4099" class="Keyword">where</a>
  <a id="Tri.aa"></a><a id="4107" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#4107" class="InductiveConstructor">aa</a> <a id="4110" class="Symbol">:</a> <a id="4112" href="plfa.part1.Quantifiers.html#4089" class="Datatype">Tri</a>
  <a id="Tri.bb"></a><a id="4118" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#4118" class="InductiveConstructor">bb</a> <a id="4121" class="Symbol">:</a> <a id="4123" href="plfa.part1.Quantifiers.html#4089" class="Datatype">Tri</a>
  <a id="Tri.cc"></a><a id="4129" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#4129" class="InductiveConstructor">cc</a> <a id="4132" class="Symbol">:</a> <a id="4134" href="plfa.part1.Quantifiers.html#4089" class="Datatype">Tri</a>
</pre>{% endraw %}Let `B` be a type indexed by `Tri`, that is `B : Tri → Set`.
Show that `∀ (x : Tri) → B x` is isomorphic to `B aa × B bb × B cc`.


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
{% raw %}<pre class="Agda"><a id="4760" class="Keyword">data</a> <a id="Σ"></a><a id="4765" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#4765" class="Datatype">Σ</a> <a id="4767" class="Symbol">(</a><a id="4768" href="plfa.part1.Quantifiers.html#4768" class="Bound">A</a> <a id="4770" class="Symbol">:</a> <a id="4772" class="PrimitiveType">Set</a><a id="4775" class="Symbol">)</a> <a id="4777" class="Symbol">(</a><a id="4778" href="plfa.part1.Quantifiers.html#4778" class="Bound">B</a> <a id="4780" class="Symbol">:</a> <a id="4782" href="plfa.part1.Quantifiers.html#4768" class="Bound">A</a> <a id="4784" class="Symbol">→</a> <a id="4786" class="PrimitiveType">Set</a><a id="4789" class="Symbol">)</a> <a id="4791" class="Symbol">:</a> <a id="4793" class="PrimitiveType">Set</a> <a id="4797" class="Keyword">where</a>
  <a id="Σ.⟨_,_⟩"></a><a id="4805" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#4805" class="InductiveConstructor Operator">⟨_,_⟩</a> <a id="4811" class="Symbol">:</a> <a id="4813" class="Symbol">(</a><a id="4814" href="plfa.part1.Quantifiers.html#4814" class="Bound">x</a> <a id="4816" class="Symbol">:</a> <a id="4818" href="plfa.part1.Quantifiers.html#4768" class="Bound">A</a><a id="4819" class="Symbol">)</a> <a id="4821" class="Symbol">→</a> <a id="4823" href="plfa.part1.Quantifiers.html#4778" class="Bound">B</a> <a id="4825" href="plfa.part1.Quantifiers.html#4814" class="Bound">x</a> <a id="4827" class="Symbol">→</a> <a id="4829" href="plfa.part1.Quantifiers.html#4765" class="Datatype">Σ</a> <a id="4831" href="plfa.part1.Quantifiers.html#4768" class="Bound">A</a> <a id="4833" href="plfa.part1.Quantifiers.html#4778" class="Bound">B</a>
</pre>{% endraw %}We define a convenient syntax for existentials as follows:
{% raw %}<pre class="Agda"><a id="Σ-syntax"></a><a id="4902" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#4902" class="Function">Σ-syntax</a> <a id="4911" class="Symbol">=</a> <a id="4913" href="plfa.part1.Quantifiers.html#4765" class="Datatype">Σ</a>
<a id="4915" class="Keyword">infix</a> <a id="4921" class="Number">2</a> <a id="4923" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#4902" class="Function">Σ-syntax</a>
<a id="4932" class="Keyword">syntax</a> <a id="4939" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#4902" class="Function">Σ-syntax</a> <a id="4948" class="Bound">A</a> <a id="4950" class="Symbol">(λ</a> <a id="4953" class="Bound">x</a> <a id="4955" class="Symbol">→</a> <a id="4957" class="Bound">B</a><a id="4958" class="Symbol">)</a> <a id="4960" class="Symbol">=</a> <a id="4962" class="Function">Σ[</a> <a id="4965" class="Bound">x</a> <a id="4967" class="Function">∈</a> <a id="4969" class="Bound">A</a> <a id="4971" class="Function">]</a> <a id="4973" class="Bound">B</a>
</pre>{% endraw %}This is our first use of a syntax declaration, which specifies that
the term on the left may be written with the syntax on the right.
The special syntax is available only when the identifier
`Σ-syntax` is imported.

Evidence that `Σ[ x ∈ A ] B x` holds is of the form
`⟨ M , N ⟩` where `M` is a term of type `A`, and `N` is evidence
that `B M` holds.

Equivalently, we could also declare existentials as a record type:
{% raw %}<pre class="Agda"><a id="5402" class="Keyword">record</a> <a id="Σ′"></a><a id="5409" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#5409" class="Record">Σ′</a> <a id="5412" class="Symbol">(</a><a id="5413" href="plfa.part1.Quantifiers.html#5413" class="Bound">A</a> <a id="5415" class="Symbol">:</a> <a id="5417" class="PrimitiveType">Set</a><a id="5420" class="Symbol">)</a> <a id="5422" class="Symbol">(</a><a id="5423" href="plfa.part1.Quantifiers.html#5423" class="Bound">B</a> <a id="5425" class="Symbol">:</a> <a id="5427" href="plfa.part1.Quantifiers.html#5413" class="Bound">A</a> <a id="5429" class="Symbol">→</a> <a id="5431" class="PrimitiveType">Set</a><a id="5434" class="Symbol">)</a> <a id="5436" class="Symbol">:</a> <a id="5438" class="PrimitiveType">Set</a> <a id="5442" class="Keyword">where</a>
  <a id="5450" class="Keyword">field</a>
    <a id="Σ′.proj₁′"></a><a id="5460" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#5460" class="Field">proj₁′</a> <a id="5467" class="Symbol">:</a> <a id="5469" href="plfa.part1.Quantifiers.html#5413" class="Bound">A</a>
    <a id="Σ′.proj₂′"></a><a id="5475" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#5475" class="Field">proj₂′</a> <a id="5482" class="Symbol">:</a> <a id="5484" href="plfa.part1.Quantifiers.html#5423" class="Bound">B</a> <a id="5486" href="plfa.part1.Quantifiers.html#5460" class="Field">proj₁′</a>
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
{% raw %}<pre class="Agda"><a id="∃"></a><a id="7133" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#7133" class="Function">∃</a> <a id="7135" class="Symbol">:</a> <a id="7137" class="Symbol">∀</a> <a id="7139" class="Symbol">{</a><a id="7140" href="plfa.part1.Quantifiers.html#7140" class="Bound">A</a> <a id="7142" class="Symbol">:</a> <a id="7144" class="PrimitiveType">Set</a><a id="7147" class="Symbol">}</a> <a id="7149" class="Symbol">(</a><a id="7150" href="plfa.part1.Quantifiers.html#7150" class="Bound">B</a> <a id="7152" class="Symbol">:</a> <a id="7154" href="plfa.part1.Quantifiers.html#7140" class="Bound">A</a> <a id="7156" class="Symbol">→</a> <a id="7158" class="PrimitiveType">Set</a><a id="7161" class="Symbol">)</a> <a id="7163" class="Symbol">→</a> <a id="7165" class="PrimitiveType">Set</a>
<a id="7169" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#7133" class="Function">∃</a> <a id="7171" class="Symbol">{</a><a id="7172" href="plfa.part1.Quantifiers.html#7172" class="Bound">A</a><a id="7173" class="Symbol">}</a> <a id="7175" href="plfa.part1.Quantifiers.html#7175" class="Bound">B</a> <a id="7177" class="Symbol">=</a> <a id="7179" href="plfa.part1.Quantifiers.html#4765" class="Datatype">Σ</a> <a id="7181" href="plfa.part1.Quantifiers.html#7172" class="Bound">A</a> <a id="7183" href="plfa.part1.Quantifiers.html#7175" class="Bound">B</a>

<a id="∃-syntax"></a><a id="7186" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#7186" class="Function">∃-syntax</a> <a id="7195" class="Symbol">=</a> <a id="7197" href="plfa.part1.Quantifiers.html#7133" class="Function">∃</a>
<a id="7199" class="Keyword">syntax</a> <a id="7206" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#7186" class="Function">∃-syntax</a> <a id="7215" class="Symbol">(λ</a> <a id="7218" class="Bound">x</a> <a id="7220" class="Symbol">→</a> <a id="7222" class="Bound">B</a><a id="7223" class="Symbol">)</a> <a id="7225" class="Symbol">=</a> <a id="7227" class="Function">∃[</a> <a id="7230" class="Bound">x</a> <a id="7232" class="Function">]</a> <a id="7234" class="Bound">B</a>
</pre>{% endraw %}The special syntax is available only when the identifier `∃-syntax` is imported.
We will tend to use this syntax, since it is shorter and more familiar.

Given evidence that `∀ x → B x → C` holds, where `C` does not contain
`x` as a free variable, and given evidence that `∃[ x ] B x` holds, we
may conclude that `C` holds:
{% raw %}<pre class="Agda"><a id="∃-elim"></a><a id="7568" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#7568" class="Function">∃-elim</a> <a id="7575" class="Symbol">:</a> <a id="7577" class="Symbol">∀</a> <a id="7579" class="Symbol">{</a><a id="7580" href="plfa.part1.Quantifiers.html#7580" class="Bound">A</a> <a id="7582" class="Symbol">:</a> <a id="7584" class="PrimitiveType">Set</a><a id="7587" class="Symbol">}</a> <a id="7589" class="Symbol">{</a><a id="7590" href="plfa.part1.Quantifiers.html#7590" class="Bound">B</a> <a id="7592" class="Symbol">:</a> <a id="7594" href="plfa.part1.Quantifiers.html#7580" class="Bound">A</a> <a id="7596" class="Symbol">→</a> <a id="7598" class="PrimitiveType">Set</a><a id="7601" class="Symbol">}</a> <a id="7603" class="Symbol">{</a><a id="7604" href="plfa.part1.Quantifiers.html#7604" class="Bound">C</a> <a id="7606" class="Symbol">:</a> <a id="7608" class="PrimitiveType">Set</a><a id="7611" class="Symbol">}</a>
  <a id="7615" class="Symbol">→</a> <a id="7617" class="Symbol">(∀</a> <a id="7620" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#7620" class="Bound">x</a> <a id="7622" class="Symbol">→</a> <a id="7624" href="plfa.part1.Quantifiers.html#7590" class="Bound">B</a> <a id="7626" href="plfa.part1.Quantifiers.html#7620" class="Bound">x</a> <a id="7628" class="Symbol">→</a> <a id="7630" href="plfa.part1.Quantifiers.html#7604" class="Bound">C</a><a id="7631" class="Symbol">)</a>
  <a id="7635" class="Symbol">→</a> <a id="7637" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#7186" class="Function">∃[</a> <a id="7640" href="plfa.part1.Quantifiers.html#7640" class="Bound">x</a> <a id="7642" href="plfa.part1.Quantifiers.html#7186" class="Function">]</a> <a id="7644" href="plfa.part1.Quantifiers.html#7590" class="Bound">B</a> <a id="7646" href="plfa.part1.Quantifiers.html#7640" class="Bound">x</a>
    <a id="7652" class="Comment">---------------</a>
  <a id="7670" class="Symbol">→</a> <a id="7672" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#7604" class="Bound">C</a>
<a id="7674" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#7568" class="Function">∃-elim</a> <a id="7681" href="plfa.part1.Quantifiers.html#7681" class="Bound">f</a> <a id="7683" href="plfa.part1.Quantifiers.html#4805" class="InductiveConstructor Operator">⟨</a> <a id="7685" href="plfa.part1.Quantifiers.html#7685" class="Bound">x</a> <a id="7687" href="plfa.part1.Quantifiers.html#4805" class="InductiveConstructor Operator">,</a> <a id="7689" href="plfa.part1.Quantifiers.html#7689" class="Bound">y</a> <a id="7691" href="plfa.part1.Quantifiers.html#4805" class="InductiveConstructor Operator">⟩</a> <a id="7693" class="Symbol">=</a> <a id="7695" href="plfa.part1.Quantifiers.html#7681" class="Bound">f</a> <a id="7697" href="plfa.part1.Quantifiers.html#7685" class="Bound">x</a> <a id="7699" href="plfa.part1.Quantifiers.html#7689" class="Bound">y</a>
</pre>{% endraw %}In other words, if we know for every `x` of type `A` that `B x`
implies `C`, and we know for some `x` of type `A` that `B x` holds,
then we may conclude that `C` holds.  This is because we may
instantiate that proof that `∀ x → B x → C` to any value `x` of type
`A` and any `y` of type `B x`, and exactly such values are provided by
the evidence for `∃[ x ] B x`.

Indeed, the converse also holds, and the two together form an isomorphism:
{% raw %}<pre class="Agda"><a id="∀∃-currying"></a><a id="8149" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#8149" class="Function">∀∃-currying</a> <a id="8161" class="Symbol">:</a> <a id="8163" class="Symbol">∀</a> <a id="8165" class="Symbol">{</a><a id="8166" href="plfa.part1.Quantifiers.html#8166" class="Bound">A</a> <a id="8168" class="Symbol">:</a> <a id="8170" class="PrimitiveType">Set</a><a id="8173" class="Symbol">}</a> <a id="8175" class="Symbol">{</a><a id="8176" href="plfa.part1.Quantifiers.html#8176" class="Bound">B</a> <a id="8178" class="Symbol">:</a> <a id="8180" href="plfa.part1.Quantifiers.html#8166" class="Bound">A</a> <a id="8182" class="Symbol">→</a> <a id="8184" class="PrimitiveType">Set</a><a id="8187" class="Symbol">}</a> <a id="8189" class="Symbol">{</a><a id="8190" href="plfa.part1.Quantifiers.html#8190" class="Bound">C</a> <a id="8192" class="Symbol">:</a> <a id="8194" class="PrimitiveType">Set</a><a id="8197" class="Symbol">}</a>
  <a id="8201" class="Symbol">→</a> <a id="8203" class="Symbol">(∀</a> <a id="8206" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#8206" class="Bound">x</a> <a id="8208" class="Symbol">→</a> <a id="8210" href="plfa.part1.Quantifiers.html#8176" class="Bound">B</a> <a id="8212" href="plfa.part1.Quantifiers.html#8206" class="Bound">x</a> <a id="8214" class="Symbol">→</a> <a id="8216" href="plfa.part1.Quantifiers.html#8190" class="Bound">C</a><a id="8217" class="Symbol">)</a> <a id="8219" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#4365" class="Record Operator">≃</a> <a id="8221" class="Symbol">(</a><a id="8222" href="plfa.part1.Quantifiers.html#7186" class="Function">∃[</a> <a id="8225" href="plfa.part1.Quantifiers.html#8225" class="Bound">x</a> <a id="8227" href="plfa.part1.Quantifiers.html#7186" class="Function">]</a> <a id="8229" href="plfa.part1.Quantifiers.html#8176" class="Bound">B</a> <a id="8231" href="plfa.part1.Quantifiers.html#8225" class="Bound">x</a> <a id="8233" class="Symbol">→</a> <a id="8235" href="plfa.part1.Quantifiers.html#8190" class="Bound">C</a><a id="8236" class="Symbol">)</a>
<a id="8238" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#8149" class="Function">∀∃-currying</a> <a id="8250" class="Symbol">=</a>
  <a id="8254" class="Keyword">record</a>
    <a id="8265" class="Symbol">{</a> <a id="8267" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#4405" class="Field">to</a>      <a id="8275" class="Symbol">=</a>  <a id="8278" class="Symbol">λ{</a> <a id="8281" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#8281" class="Bound">f</a> <a id="8283" class="Symbol">→</a> <a id="8285" class="Symbol">λ{</a> <a id="8288" href="plfa.part1.Quantifiers.html#4805" class="InductiveConstructor Operator">⟨</a> <a id="8290" href="plfa.part1.Quantifiers.html#8290" class="Bound">x</a> <a id="8292" href="plfa.part1.Quantifiers.html#4805" class="InductiveConstructor Operator">,</a> <a id="8294" href="plfa.part1.Quantifiers.html#8294" class="Bound">y</a> <a id="8296" href="plfa.part1.Quantifiers.html#4805" class="InductiveConstructor Operator">⟩</a> <a id="8298" class="Symbol">→</a> <a id="8300" href="plfa.part1.Quantifiers.html#8281" class="Bound">f</a> <a id="8302" href="plfa.part1.Quantifiers.html#8290" class="Bound">x</a> <a id="8304" href="plfa.part1.Quantifiers.html#8294" class="Bound">y</a> <a id="8306" class="Symbol">}}</a>
    <a id="8313" class="Symbol">;</a> <a id="8315" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#4422" class="Field">from</a>    <a id="8323" class="Symbol">=</a>  <a id="8326" class="Symbol">λ{</a> <a id="8329" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#8329" class="Bound">g</a> <a id="8331" class="Symbol">→</a> <a id="8333" class="Symbol">λ{</a> <a id="8336" href="plfa.part1.Quantifiers.html#8336" class="Bound">x</a> <a id="8338" class="Symbol">→</a> <a id="8340" class="Symbol">λ{</a> <a id="8343" href="plfa.part1.Quantifiers.html#8343" class="Bound">y</a> <a id="8345" class="Symbol">→</a> <a id="8347" href="plfa.part1.Quantifiers.html#8329" class="Bound">g</a> <a id="8349" href="plfa.part1.Quantifiers.html#4805" class="InductiveConstructor Operator">⟨</a> <a id="8351" href="plfa.part1.Quantifiers.html#8336" class="Bound">x</a> <a id="8353" href="plfa.part1.Quantifiers.html#4805" class="InductiveConstructor Operator">,</a> <a id="8355" href="plfa.part1.Quantifiers.html#8343" class="Bound">y</a> <a id="8357" href="plfa.part1.Quantifiers.html#4805" class="InductiveConstructor Operator">⟩</a> <a id="8359" class="Symbol">}}}</a>
    <a id="8367" class="Symbol">;</a> <a id="8369" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#4439" class="Field">from∘to</a> <a id="8377" class="Symbol">=</a>  <a id="8380" class="Symbol">λ{</a> <a id="8383" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#8383" class="Bound">f</a> <a id="8385" class="Symbol">→</a> <a id="8387" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="8392" class="Symbol">}</a>
    <a id="8398" class="Symbol">;</a> <a id="8400" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#4481" class="Field">to∘from</a> <a id="8408" class="Symbol">=</a>  <a id="8411" class="Symbol">λ{</a> <a id="8414" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#8414" class="Bound">g</a> <a id="8416" class="Symbol">→</a> <a id="8418" href="plfa.part1.Isomorphism.html#2684" class="Postulate">extensionality</a> <a id="8433" class="Symbol">λ{</a> <a id="8436" href="plfa.part1.Quantifiers.html#4805" class="InductiveConstructor Operator">⟨</a> <a id="8438" href="plfa.part1.Quantifiers.html#8438" class="Bound">x</a> <a id="8440" href="plfa.part1.Quantifiers.html#4805" class="InductiveConstructor Operator">,</a> <a id="8442" href="plfa.part1.Quantifiers.html#8442" class="Bound">y</a> <a id="8444" href="plfa.part1.Quantifiers.html#4805" class="InductiveConstructor Operator">⟩</a> <a id="8446" class="Symbol">→</a> <a id="8448" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="8453" class="Symbol">}}</a>
    <a id="8460" class="Symbol">}</a>
</pre>{% endraw %}The result can be viewed as a generalisation of currying.  Indeed, the code to
establish the isomorphism is identical to what we wrote when discussing
[implication]({{ site.baseurl }}/Connectives/#implication).

#### Exercise `∃-distrib-⊎` (recommended)

Show that existentials distribute over disjunction:
{% raw %}<pre class="Agda"><a id="8777" class="Keyword">postulate</a>
  <a id="∃-distrib-⊎"></a><a id="8789" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#8789" class="Postulate">∃-distrib-⊎</a> <a id="8801" class="Symbol">:</a> <a id="8803" class="Symbol">∀</a> <a id="8805" class="Symbol">{</a><a id="8806" href="plfa.part1.Quantifiers.html#8806" class="Bound">A</a> <a id="8808" class="Symbol">:</a> <a id="8810" class="PrimitiveType">Set</a><a id="8813" class="Symbol">}</a> <a id="8815" class="Symbol">{</a><a id="8816" href="plfa.part1.Quantifiers.html#8816" class="Bound">B</a> <a id="8818" href="plfa.part1.Quantifiers.html#8818" class="Bound">C</a> <a id="8820" class="Symbol">:</a> <a id="8822" href="plfa.part1.Quantifiers.html#8806" class="Bound">A</a> <a id="8824" class="Symbol">→</a> <a id="8826" class="PrimitiveType">Set</a><a id="8829" class="Symbol">}</a> <a id="8831" class="Symbol">→</a>
    <a id="8837" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#7186" class="Function">∃[</a> <a id="8840" href="plfa.part1.Quantifiers.html#8840" class="Bound">x</a> <a id="8842" href="plfa.part1.Quantifiers.html#7186" class="Function">]</a> <a id="8844" class="Symbol">(</a><a id="8845" href="plfa.part1.Quantifiers.html#8816" class="Bound">B</a> <a id="8847" href="plfa.part1.Quantifiers.html#8840" class="Bound">x</a> <a id="8849" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#612" class="Datatype Operator">⊎</a> <a id="8851" href="plfa.part1.Quantifiers.html#8818" class="Bound">C</a> <a id="8853" href="plfa.part1.Quantifiers.html#8840" class="Bound">x</a><a id="8854" class="Symbol">)</a> <a id="8856" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#4365" class="Record Operator">≃</a> <a id="8858" class="Symbol">(</a><a id="8859" href="plfa.part1.Quantifiers.html#7186" class="Function">∃[</a> <a id="8862" href="plfa.part1.Quantifiers.html#8862" class="Bound">x</a> <a id="8864" href="plfa.part1.Quantifiers.html#7186" class="Function">]</a> <a id="8866" href="plfa.part1.Quantifiers.html#8816" class="Bound">B</a> <a id="8868" href="plfa.part1.Quantifiers.html#8862" class="Bound">x</a><a id="8869" class="Symbol">)</a> <a id="8871" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#612" class="Datatype Operator">⊎</a> <a id="8873" class="Symbol">(</a><a id="8874" href="plfa.part1.Quantifiers.html#7186" class="Function">∃[</a> <a id="8877" href="plfa.part1.Quantifiers.html#8877" class="Bound">x</a> <a id="8879" href="plfa.part1.Quantifiers.html#7186" class="Function">]</a> <a id="8881" href="plfa.part1.Quantifiers.html#8818" class="Bound">C</a> <a id="8883" href="plfa.part1.Quantifiers.html#8877" class="Bound">x</a><a id="8884" class="Symbol">)</a>
</pre>{% endraw %}
#### Exercise `∃×-implies-×∃` (practice)

Show that an existential of conjunctions implies a conjunction of existentials:
{% raw %}<pre class="Agda"><a id="9017" class="Keyword">postulate</a>
  <a id="∃×-implies-×∃"></a><a id="9029" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#9029" class="Postulate">∃×-implies-×∃</a> <a id="9043" class="Symbol">:</a> <a id="9045" class="Symbol">∀</a> <a id="9047" class="Symbol">{</a><a id="9048" href="plfa.part1.Quantifiers.html#9048" class="Bound">A</a> <a id="9050" class="Symbol">:</a> <a id="9052" class="PrimitiveType">Set</a><a id="9055" class="Symbol">}</a> <a id="9057" class="Symbol">{</a><a id="9058" href="plfa.part1.Quantifiers.html#9058" class="Bound">B</a> <a id="9060" href="plfa.part1.Quantifiers.html#9060" class="Bound">C</a> <a id="9062" class="Symbol">:</a> <a id="9064" href="plfa.part1.Quantifiers.html#9048" class="Bound">A</a> <a id="9066" class="Symbol">→</a> <a id="9068" class="PrimitiveType">Set</a><a id="9071" class="Symbol">}</a> <a id="9073" class="Symbol">→</a>
    <a id="9079" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#7186" class="Function">∃[</a> <a id="9082" href="plfa.part1.Quantifiers.html#9082" class="Bound">x</a> <a id="9084" href="plfa.part1.Quantifiers.html#7186" class="Function">]</a> <a id="9086" class="Symbol">(</a><a id="9087" href="plfa.part1.Quantifiers.html#9058" class="Bound">B</a> <a id="9089" href="plfa.part1.Quantifiers.html#9082" class="Bound">x</a> <a id="9091" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1162" class="Function Operator">×</a> <a id="9093" href="plfa.part1.Quantifiers.html#9060" class="Bound">C</a> <a id="9095" href="plfa.part1.Quantifiers.html#9082" class="Bound">x</a><a id="9096" class="Symbol">)</a> <a id="9098" class="Symbol">→</a> <a id="9100" class="Symbol">(</a><a id="9101" href="plfa.part1.Quantifiers.html#7186" class="Function">∃[</a> <a id="9104" href="plfa.part1.Quantifiers.html#9104" class="Bound">x</a> <a id="9106" href="plfa.part1.Quantifiers.html#7186" class="Function">]</a> <a id="9108" href="plfa.part1.Quantifiers.html#9058" class="Bound">B</a> <a id="9110" href="plfa.part1.Quantifiers.html#9104" class="Bound">x</a><a id="9111" class="Symbol">)</a> <a id="9113" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1162" class="Function Operator">×</a> <a id="9115" class="Symbol">(</a><a id="9116" href="plfa.part1.Quantifiers.html#7186" class="Function">∃[</a> <a id="9119" href="plfa.part1.Quantifiers.html#9119" class="Bound">x</a> <a id="9121" href="plfa.part1.Quantifiers.html#7186" class="Function">]</a> <a id="9123" href="plfa.part1.Quantifiers.html#9060" class="Bound">C</a> <a id="9125" href="plfa.part1.Quantifiers.html#9119" class="Bound">x</a><a id="9126" class="Symbol">)</a>
</pre>{% endraw %}Does the converse hold? If so, prove; if not, explain why.

#### Exercise `∃-⊎` (practice)

Let `Tri` and `B` be as in Exercise `∀-×`.
Show that `∃[ x ] B x` is isomorphic to `B aa ⊎ B bb ⊎ B cc`.


## An existential example

Recall the definitions of `even` and `odd` from
Chapter [Relations]({{ site.baseurl }}/Relations/):
{% raw %}<pre class="Agda"><a id="9462" class="Keyword">data</a> <a id="even"></a><a id="9467" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#9467" class="Datatype">even</a> <a id="9472" class="Symbol">:</a> <a id="9474" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a> <a id="9476" class="Symbol">→</a> <a id="9478" class="PrimitiveType">Set</a>
<a id="9482" class="Keyword">data</a> <a id="odd"></a><a id="9487" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#9487" class="Datatype">odd</a>  <a id="9492" class="Symbol">:</a> <a id="9494" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a> <a id="9496" class="Symbol">→</a> <a id="9498" class="PrimitiveType">Set</a>

<a id="9503" class="Keyword">data</a> <a id="9508" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#9467" class="Datatype">even</a> <a id="9513" class="Keyword">where</a>

  <a id="even.even-zero"></a><a id="9522" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#9522" class="InductiveConstructor">even-zero</a> <a id="9532" class="Symbol">:</a> <a id="9534" href="plfa.part1.Quantifiers.html#9467" class="Datatype">even</a> <a id="9539" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a>

  <a id="even.even-suc"></a><a id="9547" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#9547" class="InductiveConstructor">even-suc</a> <a id="9556" class="Symbol">:</a> <a id="9558" class="Symbol">∀</a> <a id="9560" class="Symbol">{</a><a id="9561" href="plfa.part1.Quantifiers.html#9561" class="Bound">n</a> <a id="9563" class="Symbol">:</a> <a id="9565" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="9566" class="Symbol">}</a>
    <a id="9572" class="Symbol">→</a> <a id="9574" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#9487" class="Datatype">odd</a> <a id="9578" href="plfa.part1.Quantifiers.html#9561" class="Bound">n</a>
      <a id="9586" class="Comment">------------</a>
    <a id="9603" class="Symbol">→</a> <a id="9605" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#9467" class="Datatype">even</a> <a id="9610" class="Symbol">(</a><a id="9611" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="9615" href="plfa.part1.Quantifiers.html#9561" class="Bound">n</a><a id="9616" class="Symbol">)</a>

<a id="9619" class="Keyword">data</a> <a id="9624" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#9487" class="Datatype">odd</a> <a id="9628" class="Keyword">where</a>
  <a id="odd.odd-suc"></a><a id="9636" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#9636" class="InductiveConstructor">odd-suc</a> <a id="9644" class="Symbol">:</a> <a id="9646" class="Symbol">∀</a> <a id="9648" class="Symbol">{</a><a id="9649" href="plfa.part1.Quantifiers.html#9649" class="Bound">n</a> <a id="9651" class="Symbol">:</a> <a id="9653" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="9654" class="Symbol">}</a>
    <a id="9660" class="Symbol">→</a> <a id="9662" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#9467" class="Datatype">even</a> <a id="9667" href="plfa.part1.Quantifiers.html#9649" class="Bound">n</a>
      <a id="9675" class="Comment">-----------</a>
    <a id="9691" class="Symbol">→</a> <a id="9693" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#9487" class="Datatype">odd</a> <a id="9697" class="Symbol">(</a><a id="9698" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="9702" href="plfa.part1.Quantifiers.html#9649" class="Bound">n</a><a id="9703" class="Symbol">)</a>
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
{% raw %}<pre class="Agda"><a id="even-∃"></a><a id="10324" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#10324" class="Function">even-∃</a> <a id="10331" class="Symbol">:</a> <a id="10333" class="Symbol">∀</a> <a id="10335" class="Symbol">{</a><a id="10336" href="plfa.part1.Quantifiers.html#10336" class="Bound">n</a> <a id="10338" class="Symbol">:</a> <a id="10340" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="10341" class="Symbol">}</a> <a id="10343" class="Symbol">→</a> <a id="10345" href="plfa.part1.Quantifiers.html#9467" class="Datatype">even</a> <a id="10350" href="plfa.part1.Quantifiers.html#10336" class="Bound">n</a> <a id="10352" class="Symbol">→</a> <a id="10354" href="plfa.part1.Quantifiers.html#7186" class="Function">∃[</a> <a id="10357" href="plfa.part1.Quantifiers.html#10357" class="Bound">m</a> <a id="10359" href="plfa.part1.Quantifiers.html#7186" class="Function">]</a> <a id="10361" class="Symbol">(</a>    <a id="10366" href="plfa.part1.Quantifiers.html#10357" class="Bound">m</a> <a id="10368" href="Agda.Builtin.Nat.html#501" class="Primitive Operator">*</a> <a id="10370" class="Number">2</a> <a id="10372" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="10374" href="plfa.part1.Quantifiers.html#10336" class="Bound">n</a><a id="10375" class="Symbol">)</a>
<a id="odd-∃"></a><a id="10377" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#10377" class="Function">odd-∃</a>  <a id="10384" class="Symbol">:</a> <a id="10386" class="Symbol">∀</a> <a id="10388" class="Symbol">{</a><a id="10389" href="plfa.part1.Quantifiers.html#10389" class="Bound">n</a> <a id="10391" class="Symbol">:</a> <a id="10393" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="10394" class="Symbol">}</a> <a id="10396" class="Symbol">→</a>  <a id="10399" href="plfa.part1.Quantifiers.html#9487" class="Datatype">odd</a> <a id="10403" href="plfa.part1.Quantifiers.html#10389" class="Bound">n</a> <a id="10405" class="Symbol">→</a> <a id="10407" href="plfa.part1.Quantifiers.html#7186" class="Function">∃[</a> <a id="10410" href="plfa.part1.Quantifiers.html#10410" class="Bound">m</a> <a id="10412" href="plfa.part1.Quantifiers.html#7186" class="Function">]</a> <a id="10414" class="Symbol">(</a><a id="10415" class="Number">1</a> <a id="10417" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="10419" href="plfa.part1.Quantifiers.html#10410" class="Bound">m</a> <a id="10421" href="Agda.Builtin.Nat.html#501" class="Primitive Operator">*</a> <a id="10423" class="Number">2</a> <a id="10425" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="10427" href="plfa.part1.Quantifiers.html#10389" class="Bound">n</a><a id="10428" class="Symbol">)</a>

<a id="10431" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#10324" class="Function">even-∃</a> <a id="10438" href="plfa.part1.Quantifiers.html#9522" class="InductiveConstructor">even-zero</a>                       <a id="10470" class="Symbol">=</a>  <a id="10473" href="plfa.part1.Quantifiers.html#4805" class="InductiveConstructor Operator">⟨</a> <a id="10475" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a> <a id="10480" href="plfa.part1.Quantifiers.html#4805" class="InductiveConstructor Operator">,</a> <a id="10482" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="10487" href="plfa.part1.Quantifiers.html#4805" class="InductiveConstructor Operator">⟩</a>
<a id="10489" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#10324" class="Function">even-∃</a> <a id="10496" class="Symbol">(</a><a id="10497" href="plfa.part1.Quantifiers.html#9547" class="InductiveConstructor">even-suc</a> <a id="10506" href="plfa.part1.Quantifiers.html#10506" class="Bound">o</a><a id="10507" class="Symbol">)</a> <a id="10509" class="Keyword">with</a> <a id="10514" href="plfa.part1.Quantifiers.html#10377" class="Function">odd-∃</a> <a id="10520" href="plfa.part1.Quantifiers.html#10506" class="Bound">o</a>
<a id="10522" class="Symbol">...</a>                    <a id="10545" class="Symbol">|</a> <a id="10547" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#4805" class="InductiveConstructor Operator">⟨</a> <a id="10549" href="plfa.part1.Quantifiers.html#10549" class="Bound">m</a> <a id="10551" href="plfa.part1.Quantifiers.html#4805" class="InductiveConstructor Operator">,</a> <a id="10553" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="10558" href="plfa.part1.Quantifiers.html#4805" class="InductiveConstructor Operator">⟩</a>  <a id="10561" class="Symbol">=</a>  <a id="10564" href="plfa.part1.Quantifiers.html#4805" class="InductiveConstructor Operator">⟨</a> <a id="10566" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="10570" href="plfa.part1.Quantifiers.html#10549" class="Bound">m</a> <a id="10572" href="plfa.part1.Quantifiers.html#4805" class="InductiveConstructor Operator">,</a> <a id="10574" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="10579" href="plfa.part1.Quantifiers.html#4805" class="InductiveConstructor Operator">⟩</a>

<a id="10582" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#10377" class="Function">odd-∃</a>  <a id="10589" class="Symbol">(</a><a id="10590" href="plfa.part1.Quantifiers.html#9636" class="InductiveConstructor">odd-suc</a> <a id="10598" href="plfa.part1.Quantifiers.html#10598" class="Bound">e</a><a id="10599" class="Symbol">)</a>  <a id="10602" class="Keyword">with</a> <a id="10607" href="plfa.part1.Quantifiers.html#10324" class="Function">even-∃</a> <a id="10614" href="plfa.part1.Quantifiers.html#10598" class="Bound">e</a>
<a id="10616" class="Symbol">...</a>                    <a id="10639" class="Symbol">|</a> <a id="10641" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#4805" class="InductiveConstructor Operator">⟨</a> <a id="10643" href="plfa.part1.Quantifiers.html#10643" class="Bound">m</a> <a id="10645" href="plfa.part1.Quantifiers.html#4805" class="InductiveConstructor Operator">,</a> <a id="10647" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="10652" href="plfa.part1.Quantifiers.html#4805" class="InductiveConstructor Operator">⟩</a>  <a id="10655" class="Symbol">=</a>  <a id="10658" href="plfa.part1.Quantifiers.html#4805" class="InductiveConstructor Operator">⟨</a> <a id="10660" href="plfa.part1.Quantifiers.html#10643" class="Bound">m</a> <a id="10662" href="plfa.part1.Quantifiers.html#4805" class="InductiveConstructor Operator">,</a> <a id="10664" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="10669" href="plfa.part1.Quantifiers.html#4805" class="InductiveConstructor Operator">⟩</a>
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
{% raw %}<pre class="Agda"><a id="∃-even"></a><a id="11689" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#11689" class="Function">∃-even</a> <a id="11696" class="Symbol">:</a> <a id="11698" class="Symbol">∀</a> <a id="11700" class="Symbol">{</a><a id="11701" href="plfa.part1.Quantifiers.html#11701" class="Bound">n</a> <a id="11703" class="Symbol">:</a> <a id="11705" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="11706" class="Symbol">}</a> <a id="11708" class="Symbol">→</a> <a id="11710" href="plfa.part1.Quantifiers.html#7186" class="Function">∃[</a> <a id="11713" href="plfa.part1.Quantifiers.html#11713" class="Bound">m</a> <a id="11715" href="plfa.part1.Quantifiers.html#7186" class="Function">]</a> <a id="11717" class="Symbol">(</a>    <a id="11722" href="plfa.part1.Quantifiers.html#11713" class="Bound">m</a> <a id="11724" href="Agda.Builtin.Nat.html#501" class="Primitive Operator">*</a> <a id="11726" class="Number">2</a> <a id="11728" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="11730" href="plfa.part1.Quantifiers.html#11701" class="Bound">n</a><a id="11731" class="Symbol">)</a> <a id="11733" class="Symbol">→</a> <a id="11735" href="plfa.part1.Quantifiers.html#9467" class="Datatype">even</a> <a id="11740" href="plfa.part1.Quantifiers.html#11701" class="Bound">n</a>
<a id="∃-odd"></a><a id="11742" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#11742" class="Function">∃-odd</a>  <a id="11749" class="Symbol">:</a> <a id="11751" class="Symbol">∀</a> <a id="11753" class="Symbol">{</a><a id="11754" href="plfa.part1.Quantifiers.html#11754" class="Bound">n</a> <a id="11756" class="Symbol">:</a> <a id="11758" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="11759" class="Symbol">}</a> <a id="11761" class="Symbol">→</a> <a id="11763" href="plfa.part1.Quantifiers.html#7186" class="Function">∃[</a> <a id="11766" href="plfa.part1.Quantifiers.html#11766" class="Bound">m</a> <a id="11768" href="plfa.part1.Quantifiers.html#7186" class="Function">]</a> <a id="11770" class="Symbol">(</a><a id="11771" class="Number">1</a> <a id="11773" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="11775" href="plfa.part1.Quantifiers.html#11766" class="Bound">m</a> <a id="11777" href="Agda.Builtin.Nat.html#501" class="Primitive Operator">*</a> <a id="11779" class="Number">2</a> <a id="11781" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="11783" href="plfa.part1.Quantifiers.html#11754" class="Bound">n</a><a id="11784" class="Symbol">)</a> <a id="11786" class="Symbol">→</a>  <a id="11789" href="plfa.part1.Quantifiers.html#9487" class="Datatype">odd</a> <a id="11793" href="plfa.part1.Quantifiers.html#11754" class="Bound">n</a>

<a id="11796" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#11689" class="Function">∃-even</a> <a id="11803" href="plfa.part1.Quantifiers.html#4805" class="InductiveConstructor Operator">⟨</a>  <a id="11806" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a> <a id="11811" href="plfa.part1.Quantifiers.html#4805" class="InductiveConstructor Operator">,</a> <a id="11813" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="11818" href="plfa.part1.Quantifiers.html#4805" class="InductiveConstructor Operator">⟩</a>  <a id="11821" class="Symbol">=</a>  <a id="11824" href="plfa.part1.Quantifiers.html#9522" class="InductiveConstructor">even-zero</a>
<a id="11834" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#11689" class="Function">∃-even</a> <a id="11841" href="plfa.part1.Quantifiers.html#4805" class="InductiveConstructor Operator">⟨</a> <a id="11843" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="11847" href="plfa.part1.Quantifiers.html#11847" class="Bound">m</a> <a id="11849" href="plfa.part1.Quantifiers.html#4805" class="InductiveConstructor Operator">,</a> <a id="11851" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="11856" href="plfa.part1.Quantifiers.html#4805" class="InductiveConstructor Operator">⟩</a>  <a id="11859" class="Symbol">=</a>  <a id="11862" href="plfa.part1.Quantifiers.html#9547" class="InductiveConstructor">even-suc</a> <a id="11871" class="Symbol">(</a><a id="11872" href="plfa.part1.Quantifiers.html#11742" class="Function">∃-odd</a> <a id="11878" href="plfa.part1.Quantifiers.html#4805" class="InductiveConstructor Operator">⟨</a> <a id="11880" href="plfa.part1.Quantifiers.html#11847" class="Bound">m</a> <a id="11882" href="plfa.part1.Quantifiers.html#4805" class="InductiveConstructor Operator">,</a> <a id="11884" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="11889" href="plfa.part1.Quantifiers.html#4805" class="InductiveConstructor Operator">⟩</a><a id="11890" class="Symbol">)</a>

<a id="11893" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#11742" class="Function">∃-odd</a>  <a id="11900" href="plfa.part1.Quantifiers.html#4805" class="InductiveConstructor Operator">⟨</a>     <a id="11906" href="plfa.part1.Quantifiers.html#11906" class="Bound">m</a> <a id="11908" href="plfa.part1.Quantifiers.html#4805" class="InductiveConstructor Operator">,</a> <a id="11910" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="11915" href="plfa.part1.Quantifiers.html#4805" class="InductiveConstructor Operator">⟩</a>  <a id="11918" class="Symbol">=</a>  <a id="11921" href="plfa.part1.Quantifiers.html#9636" class="InductiveConstructor">odd-suc</a> <a id="11929" class="Symbol">(</a><a id="11930" href="plfa.part1.Quantifiers.html#11689" class="Function">∃-even</a> <a id="11937" href="plfa.part1.Quantifiers.html#4805" class="InductiveConstructor Operator">⟨</a> <a id="11939" href="plfa.part1.Quantifiers.html#11906" class="Bound">m</a> <a id="11941" href="plfa.part1.Quantifiers.html#4805" class="InductiveConstructor Operator">,</a> <a id="11943" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="11948" href="plfa.part1.Quantifiers.html#4805" class="InductiveConstructor Operator">⟩</a><a id="11949" class="Symbol">)</a>
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

{% raw %}<pre class="Agda"><a id="12954" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}
#### Exercise `∃-+-≤` (practice)

Show that `y ≤ z` holds if and only if there exists a `x` such that
`x + y ≡ z`.

{% raw %}<pre class="Agda"><a id="13102" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}

## Existentials, Universals, and Negation

Negation of an existential is isomorphic to the universal
of a negation.  Considering that existentials are generalised
disjunction and universals are generalised conjunction, this
result is analogous to the one which tells us that negation
of a disjunction is isomorphic to a conjunction of negations:
{% raw %}<pre class="Agda"><a id="¬∃≃∀¬"></a><a id="13481" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#13481" class="Function">¬∃≃∀¬</a> <a id="13487" class="Symbol">:</a> <a id="13489" class="Symbol">∀</a> <a id="13491" class="Symbol">{</a><a id="13492" href="plfa.part1.Quantifiers.html#13492" class="Bound">A</a> <a id="13494" class="Symbol">:</a> <a id="13496" class="PrimitiveType">Set</a><a id="13499" class="Symbol">}</a> <a id="13501" class="Symbol">{</a><a id="13502" href="plfa.part1.Quantifiers.html#13502" class="Bound">B</a> <a id="13504" class="Symbol">:</a> <a id="13506" href="plfa.part1.Quantifiers.html#13492" class="Bound">A</a> <a id="13508" class="Symbol">→</a> <a id="13510" class="PrimitiveType">Set</a><a id="13513" class="Symbol">}</a>
  <a id="13517" class="Symbol">→</a> <a id="13519" class="Symbol">(</a><a id="13520" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#535" class="Function Operator">¬</a> <a id="13522" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#7186" class="Function">∃[</a> <a id="13525" href="plfa.part1.Quantifiers.html#13525" class="Bound">x</a> <a id="13527" href="plfa.part1.Quantifiers.html#7186" class="Function">]</a> <a id="13529" href="plfa.part1.Quantifiers.html#13502" class="Bound">B</a> <a id="13531" href="plfa.part1.Quantifiers.html#13525" class="Bound">x</a><a id="13532" class="Symbol">)</a> <a id="13534" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#4365" class="Record Operator">≃</a> <a id="13536" class="Symbol">∀</a> <a id="13538" href="plfa.part1.Quantifiers.html#13538" class="Bound">x</a> <a id="13540" class="Symbol">→</a> <a id="13542" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#535" class="Function Operator">¬</a> <a id="13544" href="plfa.part1.Quantifiers.html#13502" class="Bound">B</a> <a id="13546" href="plfa.part1.Quantifiers.html#13538" class="Bound">x</a>
<a id="13548" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#13481" class="Function">¬∃≃∀¬</a> <a id="13554" class="Symbol">=</a>
  <a id="13558" class="Keyword">record</a>
    <a id="13569" class="Symbol">{</a> <a id="13571" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#4405" class="Field">to</a>      <a id="13579" class="Symbol">=</a>  <a id="13582" class="Symbol">λ{</a> <a id="13585" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#13585" class="Bound">¬∃xy</a> <a id="13590" href="plfa.part1.Quantifiers.html#13590" class="Bound">x</a> <a id="13592" href="plfa.part1.Quantifiers.html#13592" class="Bound">y</a> <a id="13594" class="Symbol">→</a> <a id="13596" href="plfa.part1.Quantifiers.html#13585" class="Bound">¬∃xy</a> <a id="13601" href="plfa.part1.Quantifiers.html#4805" class="InductiveConstructor Operator">⟨</a> <a id="13603" href="plfa.part1.Quantifiers.html#13590" class="Bound">x</a> <a id="13605" href="plfa.part1.Quantifiers.html#4805" class="InductiveConstructor Operator">,</a> <a id="13607" href="plfa.part1.Quantifiers.html#13592" class="Bound">y</a> <a id="13609" href="plfa.part1.Quantifiers.html#4805" class="InductiveConstructor Operator">⟩</a> <a id="13611" class="Symbol">}</a>
    <a id="13617" class="Symbol">;</a> <a id="13619" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#4422" class="Field">from</a>    <a id="13627" class="Symbol">=</a>  <a id="13630" class="Symbol">λ{</a> <a id="13633" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#13633" class="Bound">∀¬xy</a> <a id="13638" href="plfa.part1.Quantifiers.html#4805" class="InductiveConstructor Operator">⟨</a> <a id="13640" href="plfa.part1.Quantifiers.html#13640" class="Bound">x</a> <a id="13642" href="plfa.part1.Quantifiers.html#4805" class="InductiveConstructor Operator">,</a> <a id="13644" href="plfa.part1.Quantifiers.html#13644" class="Bound">y</a> <a id="13646" href="plfa.part1.Quantifiers.html#4805" class="InductiveConstructor Operator">⟩</a> <a id="13648" class="Symbol">→</a> <a id="13650" href="plfa.part1.Quantifiers.html#13633" class="Bound">∀¬xy</a> <a id="13655" href="plfa.part1.Quantifiers.html#13640" class="Bound">x</a> <a id="13657" href="plfa.part1.Quantifiers.html#13644" class="Bound">y</a> <a id="13659" class="Symbol">}</a>
    <a id="13665" class="Symbol">;</a> <a id="13667" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#4439" class="Field">from∘to</a> <a id="13675" class="Symbol">=</a>  <a id="13678" class="Symbol">λ{</a> <a id="13681" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#13681" class="Bound">¬∃xy</a> <a id="13686" class="Symbol">→</a> <a id="13688" href="plfa.part1.Isomorphism.html#2684" class="Postulate">extensionality</a> <a id="13703" class="Symbol">λ{</a> <a id="13706" href="plfa.part1.Quantifiers.html#4805" class="InductiveConstructor Operator">⟨</a> <a id="13708" href="plfa.part1.Quantifiers.html#13708" class="Bound">x</a> <a id="13710" href="plfa.part1.Quantifiers.html#4805" class="InductiveConstructor Operator">,</a> <a id="13712" href="plfa.part1.Quantifiers.html#13712" class="Bound">y</a> <a id="13714" href="plfa.part1.Quantifiers.html#4805" class="InductiveConstructor Operator">⟩</a> <a id="13716" class="Symbol">→</a> <a id="13718" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="13723" class="Symbol">}</a> <a id="13725" class="Symbol">}</a>
    <a id="13731" class="Symbol">;</a> <a id="13733" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#4481" class="Field">to∘from</a> <a id="13741" class="Symbol">=</a>  <a id="13744" class="Symbol">λ{</a> <a id="13747" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#13747" class="Bound">∀¬xy</a> <a id="13752" class="Symbol">→</a> <a id="13754" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="13759" class="Symbol">}</a>
    <a id="13765" class="Symbol">}</a>
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
{% raw %}<pre class="Agda"><a id="14582" class="Keyword">postulate</a>
  <a id="∃¬-implies-¬∀"></a><a id="14594" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#14594" class="Postulate">∃¬-implies-¬∀</a> <a id="14608" class="Symbol">:</a> <a id="14610" class="Symbol">∀</a> <a id="14612" class="Symbol">{</a><a id="14613" href="plfa.part1.Quantifiers.html#14613" class="Bound">A</a> <a id="14615" class="Symbol">:</a> <a id="14617" class="PrimitiveType">Set</a><a id="14620" class="Symbol">}</a> <a id="14622" class="Symbol">{</a><a id="14623" href="plfa.part1.Quantifiers.html#14623" class="Bound">B</a> <a id="14625" class="Symbol">:</a> <a id="14627" href="plfa.part1.Quantifiers.html#14613" class="Bound">A</a> <a id="14629" class="Symbol">→</a> <a id="14631" class="PrimitiveType">Set</a><a id="14634" class="Symbol">}</a>
    <a id="14640" class="Symbol">→</a> <a id="14642" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#7186" class="Function">∃[</a> <a id="14645" href="plfa.part1.Quantifiers.html#14645" class="Bound">x</a> <a id="14647" href="plfa.part1.Quantifiers.html#7186" class="Function">]</a> <a id="14649" class="Symbol">(</a><a id="14650" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#535" class="Function Operator">¬</a> <a id="14652" href="plfa.part1.Quantifiers.html#14623" class="Bound">B</a> <a id="14654" href="plfa.part1.Quantifiers.html#14645" class="Bound">x</a><a id="14655" class="Symbol">)</a>
      <a id="14663" class="Comment">--------------</a>
    <a id="14682" class="Symbol">→</a> <a id="14684" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#535" class="Function Operator">¬</a> <a id="14686" class="Symbol">(∀</a> <a id="14689" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#14689" class="Bound">x</a> <a id="14691" class="Symbol">→</a> <a id="14693" href="plfa.part1.Quantifiers.html#14623" class="Bound">B</a> <a id="14695" href="plfa.part1.Quantifiers.html#14689" class="Bound">x</a><a id="14696" class="Symbol">)</a>
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

We recommend proving following lemmas which show that, for a given
binary number `b`, there is only one proof of `One b` and similarly
for `Can b`.

    ≡One : ∀{b : Bin} (o o' : One b) → o ≡ o'
    
    ≡Can : ∀{b : Bin} (cb : Can b) (cb' : Can b) → cb ≡ cb'

The proof of `to∘from` is tricky. We recommend proving the following lemma

    to∘from-aux : ∀ (b : Bin) (cb : Can b) → to (from b) ≡ b
                → _≡_ {_} {∃[ b ](Can b)} ⟨ to (from b) , canon-to (from b) ⟩ ⟨ b , cb ⟩

You cannot immediately use `≡Can` to equate `canon-to (from b)` and
`cb` because they have different types: `Can (to (from b))` and `Can b`
respectively.  You must first get their types to be equal, which
can be done by changing the type of `cb` using `rewrite`.

{% raw %}<pre class="Agda"><a id="16192" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}

## Standard library

Definitions similar to those in this chapter can be found in the standard library:
{% raw %}<pre class="Agda"><a id="16329" class="Keyword">import</a> <a id="16336" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html" class="Module">Data.Product</a> <a id="16349" class="Keyword">using</a> <a id="16355" class="Symbol">(</a><a id="16356" href="Agda.Builtin.Sigma.html#139" class="Record">Σ</a><a id="16357" class="Symbol">;</a> <a id="16359" href="Agda.Builtin.Sigma.html#209" class="InductiveConstructor Operator">_,_</a><a id="16362" class="Symbol">;</a> <a id="16364" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1364" class="Function">∃</a><a id="16365" class="Symbol">;</a> <a id="16367" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#911" class="Function">Σ-syntax</a><a id="16375" class="Symbol">;</a> <a id="16377" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1783" class="Function">∃-syntax</a><a id="16385" class="Symbol">)</a>
</pre>{% endraw %}

## Unicode

This chapter uses the following unicode:

    Π  U+03A0  GREEK CAPITAL LETTER PI (\Pi)
    Σ  U+03A3  GREEK CAPITAL LETTER SIGMA (\Sigma)
    ∃  U+2203  THERE EXISTS (\ex, \exists)
