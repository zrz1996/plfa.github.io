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
{% raw %}<pre class="Agda"><a id="4857" class="Keyword">data</a> <a id="Σ"></a><a id="4862" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#4862" class="Datatype">Σ</a> <a id="4864" class="Symbol">(</a><a id="4865" href="plfa.part1.Quantifiers.html#4865" class="Bound">A</a> <a id="4867" class="Symbol">:</a> <a id="4869" class="PrimitiveType">Set</a><a id="4872" class="Symbol">)</a> <a id="4874" class="Symbol">(</a><a id="4875" href="plfa.part1.Quantifiers.html#4875" class="Bound">B</a> <a id="4877" class="Symbol">:</a> <a id="4879" href="plfa.part1.Quantifiers.html#4865" class="Bound">A</a> <a id="4881" class="Symbol">→</a> <a id="4883" class="PrimitiveType">Set</a><a id="4886" class="Symbol">)</a> <a id="4888" class="Symbol">:</a> <a id="4890" class="PrimitiveType">Set</a> <a id="4894" class="Keyword">where</a>
  <a id="Σ.⟨_,_⟩"></a><a id="4902" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#4902" class="InductiveConstructor Operator">⟨_,_⟩</a> <a id="4908" class="Symbol">:</a> <a id="4910" class="Symbol">(</a><a id="4911" href="plfa.part1.Quantifiers.html#4911" class="Bound">x</a> <a id="4913" class="Symbol">:</a> <a id="4915" href="plfa.part1.Quantifiers.html#4865" class="Bound">A</a><a id="4916" class="Symbol">)</a> <a id="4918" class="Symbol">→</a> <a id="4920" href="plfa.part1.Quantifiers.html#4875" class="Bound">B</a> <a id="4922" href="plfa.part1.Quantifiers.html#4911" class="Bound">x</a> <a id="4924" class="Symbol">→</a> <a id="4926" href="plfa.part1.Quantifiers.html#4862" class="Datatype">Σ</a> <a id="4928" href="plfa.part1.Quantifiers.html#4865" class="Bound">A</a> <a id="4930" href="plfa.part1.Quantifiers.html#4875" class="Bound">B</a>
</pre>{% endraw %}We define a convenient syntax for existentials as follows:
{% raw %}<pre class="Agda"><a id="Σ-syntax"></a><a id="4999" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#4999" class="Function">Σ-syntax</a> <a id="5008" class="Symbol">=</a> <a id="5010" href="plfa.part1.Quantifiers.html#4862" class="Datatype">Σ</a>
<a id="5012" class="Keyword">infix</a> <a id="5018" class="Number">2</a> <a id="5020" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#4999" class="Function">Σ-syntax</a>
<a id="5029" class="Keyword">syntax</a> <a id="5036" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#4999" class="Function">Σ-syntax</a> <a id="5045" class="Bound">A</a> <a id="5047" class="Symbol">(λ</a> <a id="5050" class="Bound">x</a> <a id="5052" class="Symbol">→</a> <a id="5054" class="Bound">B</a><a id="5055" class="Symbol">)</a> <a id="5057" class="Symbol">=</a> <a id="5059" class="Function">Σ[</a> <a id="5062" class="Bound">x</a> <a id="5064" class="Function">∈</a> <a id="5066" class="Bound">A</a> <a id="5068" class="Function">]</a> <a id="5070" class="Bound">B</a>
</pre>{% endraw %}This is our first use of a syntax declaration, which specifies that
the term on the left may be written with the syntax on the right.
The special syntax is available only when the identifier
`Σ-syntax` is imported.

Evidence that `Σ[ x ∈ A ] B x` holds is of the form
`⟨ M , N ⟩` where `M` is a term of type `A`, and `N` is evidence
that `B M` holds.

Equivalently, we could also declare existentials as a record type:
{% raw %}<pre class="Agda"><a id="5499" class="Keyword">record</a> <a id="Σ′"></a><a id="5506" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#5506" class="Record">Σ′</a> <a id="5509" class="Symbol">(</a><a id="5510" href="plfa.part1.Quantifiers.html#5510" class="Bound">A</a> <a id="5512" class="Symbol">:</a> <a id="5514" class="PrimitiveType">Set</a><a id="5517" class="Symbol">)</a> <a id="5519" class="Symbol">(</a><a id="5520" href="plfa.part1.Quantifiers.html#5520" class="Bound">B</a> <a id="5522" class="Symbol">:</a> <a id="5524" href="plfa.part1.Quantifiers.html#5510" class="Bound">A</a> <a id="5526" class="Symbol">→</a> <a id="5528" class="PrimitiveType">Set</a><a id="5531" class="Symbol">)</a> <a id="5533" class="Symbol">:</a> <a id="5535" class="PrimitiveType">Set</a> <a id="5539" class="Keyword">where</a>
  <a id="5547" class="Keyword">field</a>
    <a id="Σ′.proj₁′"></a><a id="5557" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#5557" class="Field">proj₁′</a> <a id="5564" class="Symbol">:</a> <a id="5566" href="plfa.part1.Quantifiers.html#5510" class="Bound">A</a>
    <a id="Σ′.proj₂′"></a><a id="5572" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#5572" class="Field">proj₂′</a> <a id="5579" class="Symbol">:</a> <a id="5581" href="plfa.part1.Quantifiers.html#5520" class="Bound">B</a> <a id="5583" href="plfa.part1.Quantifiers.html#5557" class="Field">proj₁′</a>
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
{% raw %}<pre class="Agda"><a id="∃"></a><a id="7230" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#7230" class="Function">∃</a> <a id="7232" class="Symbol">:</a> <a id="7234" class="Symbol">∀</a> <a id="7236" class="Symbol">{</a><a id="7237" href="plfa.part1.Quantifiers.html#7237" class="Bound">A</a> <a id="7239" class="Symbol">:</a> <a id="7241" class="PrimitiveType">Set</a><a id="7244" class="Symbol">}</a> <a id="7246" class="Symbol">(</a><a id="7247" href="plfa.part1.Quantifiers.html#7247" class="Bound">B</a> <a id="7249" class="Symbol">:</a> <a id="7251" href="plfa.part1.Quantifiers.html#7237" class="Bound">A</a> <a id="7253" class="Symbol">→</a> <a id="7255" class="PrimitiveType">Set</a><a id="7258" class="Symbol">)</a> <a id="7260" class="Symbol">→</a> <a id="7262" class="PrimitiveType">Set</a>
<a id="7266" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#7230" class="Function">∃</a> <a id="7268" class="Symbol">{</a><a id="7269" href="plfa.part1.Quantifiers.html#7269" class="Bound">A</a><a id="7270" class="Symbol">}</a> <a id="7272" href="plfa.part1.Quantifiers.html#7272" class="Bound">B</a> <a id="7274" class="Symbol">=</a> <a id="7276" href="plfa.part1.Quantifiers.html#4862" class="Datatype">Σ</a> <a id="7278" href="plfa.part1.Quantifiers.html#7269" class="Bound">A</a> <a id="7280" href="plfa.part1.Quantifiers.html#7272" class="Bound">B</a>

<a id="∃-syntax"></a><a id="7283" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#7283" class="Function">∃-syntax</a> <a id="7292" class="Symbol">=</a> <a id="7294" href="plfa.part1.Quantifiers.html#7230" class="Function">∃</a>
<a id="7296" class="Keyword">syntax</a> <a id="7303" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#7283" class="Function">∃-syntax</a> <a id="7312" class="Symbol">(λ</a> <a id="7315" class="Bound">x</a> <a id="7317" class="Symbol">→</a> <a id="7319" class="Bound">B</a><a id="7320" class="Symbol">)</a> <a id="7322" class="Symbol">=</a> <a id="7324" class="Function">∃[</a> <a id="7327" class="Bound">x</a> <a id="7329" class="Function">]</a> <a id="7331" class="Bound">B</a>
</pre>{% endraw %}The special syntax is available only when the identifier `∃-syntax` is imported.
We will tend to use this syntax, since it is shorter and more familiar.

Given evidence that `∀ x → B x → C` holds, where `C` does not contain
`x` as a free variable, and given evidence that `∃[ x ] B x` holds, we
may conclude that `C` holds:
{% raw %}<pre class="Agda"><a id="∃-elim"></a><a id="7665" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#7665" class="Function">∃-elim</a> <a id="7672" class="Symbol">:</a> <a id="7674" class="Symbol">∀</a> <a id="7676" class="Symbol">{</a><a id="7677" href="plfa.part1.Quantifiers.html#7677" class="Bound">A</a> <a id="7679" class="Symbol">:</a> <a id="7681" class="PrimitiveType">Set</a><a id="7684" class="Symbol">}</a> <a id="7686" class="Symbol">{</a><a id="7687" href="plfa.part1.Quantifiers.html#7687" class="Bound">B</a> <a id="7689" class="Symbol">:</a> <a id="7691" href="plfa.part1.Quantifiers.html#7677" class="Bound">A</a> <a id="7693" class="Symbol">→</a> <a id="7695" class="PrimitiveType">Set</a><a id="7698" class="Symbol">}</a> <a id="7700" class="Symbol">{</a><a id="7701" href="plfa.part1.Quantifiers.html#7701" class="Bound">C</a> <a id="7703" class="Symbol">:</a> <a id="7705" class="PrimitiveType">Set</a><a id="7708" class="Symbol">}</a>
  <a id="7712" class="Symbol">→</a> <a id="7714" class="Symbol">(∀</a> <a id="7717" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#7717" class="Bound">x</a> <a id="7719" class="Symbol">→</a> <a id="7721" href="plfa.part1.Quantifiers.html#7687" class="Bound">B</a> <a id="7723" href="plfa.part1.Quantifiers.html#7717" class="Bound">x</a> <a id="7725" class="Symbol">→</a> <a id="7727" href="plfa.part1.Quantifiers.html#7701" class="Bound">C</a><a id="7728" class="Symbol">)</a>
  <a id="7732" class="Symbol">→</a> <a id="7734" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#7283" class="Function">∃[</a> <a id="7737" href="plfa.part1.Quantifiers.html#7737" class="Bound">x</a> <a id="7739" href="plfa.part1.Quantifiers.html#7283" class="Function">]</a> <a id="7741" href="plfa.part1.Quantifiers.html#7687" class="Bound">B</a> <a id="7743" href="plfa.part1.Quantifiers.html#7737" class="Bound">x</a>
    <a id="7749" class="Comment">---------------</a>
  <a id="7767" class="Symbol">→</a> <a id="7769" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#7701" class="Bound">C</a>
<a id="7771" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#7665" class="Function">∃-elim</a> <a id="7778" href="plfa.part1.Quantifiers.html#7778" class="Bound">f</a> <a id="7780" href="plfa.part1.Quantifiers.html#4902" class="InductiveConstructor Operator">⟨</a> <a id="7782" href="plfa.part1.Quantifiers.html#7782" class="Bound">x</a> <a id="7784" href="plfa.part1.Quantifiers.html#4902" class="InductiveConstructor Operator">,</a> <a id="7786" href="plfa.part1.Quantifiers.html#7786" class="Bound">y</a> <a id="7788" href="plfa.part1.Quantifiers.html#4902" class="InductiveConstructor Operator">⟩</a> <a id="7790" class="Symbol">=</a> <a id="7792" href="plfa.part1.Quantifiers.html#7778" class="Bound">f</a> <a id="7794" href="plfa.part1.Quantifiers.html#7782" class="Bound">x</a> <a id="7796" href="plfa.part1.Quantifiers.html#7786" class="Bound">y</a>
</pre>{% endraw %}In other words, if we know for every `x` of type `A` that `B x`
implies `C`, and we know for some `x` of type `A` that `B x` holds,
then we may conclude that `C` holds.  This is because we may
instantiate that proof that `∀ x → B x → C` to any value `x` of type
`A` and any `y` of type `B x`, and exactly such values are provided by
the evidence for `∃[ x ] B x`.

Indeed, the converse also holds, and the two together form an isomorphism:
{% raw %}<pre class="Agda"><a id="∀∃-currying"></a><a id="8246" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#8246" class="Function">∀∃-currying</a> <a id="8258" class="Symbol">:</a> <a id="8260" class="Symbol">∀</a> <a id="8262" class="Symbol">{</a><a id="8263" href="plfa.part1.Quantifiers.html#8263" class="Bound">A</a> <a id="8265" class="Symbol">:</a> <a id="8267" class="PrimitiveType">Set</a><a id="8270" class="Symbol">}</a> <a id="8272" class="Symbol">{</a><a id="8273" href="plfa.part1.Quantifiers.html#8273" class="Bound">B</a> <a id="8275" class="Symbol">:</a> <a id="8277" href="plfa.part1.Quantifiers.html#8263" class="Bound">A</a> <a id="8279" class="Symbol">→</a> <a id="8281" class="PrimitiveType">Set</a><a id="8284" class="Symbol">}</a> <a id="8286" class="Symbol">{</a><a id="8287" href="plfa.part1.Quantifiers.html#8287" class="Bound">C</a> <a id="8289" class="Symbol">:</a> <a id="8291" class="PrimitiveType">Set</a><a id="8294" class="Symbol">}</a>
  <a id="8298" class="Symbol">→</a> <a id="8300" class="Symbol">(∀</a> <a id="8303" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#8303" class="Bound">x</a> <a id="8305" class="Symbol">→</a> <a id="8307" href="plfa.part1.Quantifiers.html#8273" class="Bound">B</a> <a id="8309" href="plfa.part1.Quantifiers.html#8303" class="Bound">x</a> <a id="8311" class="Symbol">→</a> <a id="8313" href="plfa.part1.Quantifiers.html#8287" class="Bound">C</a><a id="8314" class="Symbol">)</a> <a id="8316" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#4365" class="Record Operator">≃</a> <a id="8318" class="Symbol">(</a><a id="8319" href="plfa.part1.Quantifiers.html#7283" class="Function">∃[</a> <a id="8322" href="plfa.part1.Quantifiers.html#8322" class="Bound">x</a> <a id="8324" href="plfa.part1.Quantifiers.html#7283" class="Function">]</a> <a id="8326" href="plfa.part1.Quantifiers.html#8273" class="Bound">B</a> <a id="8328" href="plfa.part1.Quantifiers.html#8322" class="Bound">x</a> <a id="8330" class="Symbol">→</a> <a id="8332" href="plfa.part1.Quantifiers.html#8287" class="Bound">C</a><a id="8333" class="Symbol">)</a>
<a id="8335" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#8246" class="Function">∀∃-currying</a> <a id="8347" class="Symbol">=</a>
  <a id="8351" class="Keyword">record</a>
    <a id="8362" class="Symbol">{</a> <a id="8364" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#4405" class="Field">to</a>      <a id="8372" class="Symbol">=</a>  <a id="8375" class="Symbol">λ{</a> <a id="8378" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#8378" class="Bound">f</a> <a id="8380" class="Symbol">→</a> <a id="8382" class="Symbol">λ{</a> <a id="8385" href="plfa.part1.Quantifiers.html#4902" class="InductiveConstructor Operator">⟨</a> <a id="8387" href="plfa.part1.Quantifiers.html#8387" class="Bound">x</a> <a id="8389" href="plfa.part1.Quantifiers.html#4902" class="InductiveConstructor Operator">,</a> <a id="8391" href="plfa.part1.Quantifiers.html#8391" class="Bound">y</a> <a id="8393" href="plfa.part1.Quantifiers.html#4902" class="InductiveConstructor Operator">⟩</a> <a id="8395" class="Symbol">→</a> <a id="8397" href="plfa.part1.Quantifiers.html#8378" class="Bound">f</a> <a id="8399" href="plfa.part1.Quantifiers.html#8387" class="Bound">x</a> <a id="8401" href="plfa.part1.Quantifiers.html#8391" class="Bound">y</a> <a id="8403" class="Symbol">}}</a>
    <a id="8410" class="Symbol">;</a> <a id="8412" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#4422" class="Field">from</a>    <a id="8420" class="Symbol">=</a>  <a id="8423" class="Symbol">λ{</a> <a id="8426" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#8426" class="Bound">g</a> <a id="8428" class="Symbol">→</a> <a id="8430" class="Symbol">λ{</a> <a id="8433" href="plfa.part1.Quantifiers.html#8433" class="Bound">x</a> <a id="8435" class="Symbol">→</a> <a id="8437" class="Symbol">λ{</a> <a id="8440" href="plfa.part1.Quantifiers.html#8440" class="Bound">y</a> <a id="8442" class="Symbol">→</a> <a id="8444" href="plfa.part1.Quantifiers.html#8426" class="Bound">g</a> <a id="8446" href="plfa.part1.Quantifiers.html#4902" class="InductiveConstructor Operator">⟨</a> <a id="8448" href="plfa.part1.Quantifiers.html#8433" class="Bound">x</a> <a id="8450" href="plfa.part1.Quantifiers.html#4902" class="InductiveConstructor Operator">,</a> <a id="8452" href="plfa.part1.Quantifiers.html#8440" class="Bound">y</a> <a id="8454" href="plfa.part1.Quantifiers.html#4902" class="InductiveConstructor Operator">⟩</a> <a id="8456" class="Symbol">}}}</a>
    <a id="8464" class="Symbol">;</a> <a id="8466" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#4439" class="Field">from∘to</a> <a id="8474" class="Symbol">=</a>  <a id="8477" class="Symbol">λ{</a> <a id="8480" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#8480" class="Bound">f</a> <a id="8482" class="Symbol">→</a> <a id="8484" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="8489" class="Symbol">}</a>
    <a id="8495" class="Symbol">;</a> <a id="8497" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#4481" class="Field">to∘from</a> <a id="8505" class="Symbol">=</a>  <a id="8508" class="Symbol">λ{</a> <a id="8511" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#8511" class="Bound">g</a> <a id="8513" class="Symbol">→</a> <a id="8515" href="plfa.part1.Isomorphism.html#2684" class="Postulate">extensionality</a> <a id="8530" class="Symbol">λ{</a> <a id="8533" href="plfa.part1.Quantifiers.html#4902" class="InductiveConstructor Operator">⟨</a> <a id="8535" href="plfa.part1.Quantifiers.html#8535" class="Bound">x</a> <a id="8537" href="plfa.part1.Quantifiers.html#4902" class="InductiveConstructor Operator">,</a> <a id="8539" href="plfa.part1.Quantifiers.html#8539" class="Bound">y</a> <a id="8541" href="plfa.part1.Quantifiers.html#4902" class="InductiveConstructor Operator">⟩</a> <a id="8543" class="Symbol">→</a> <a id="8545" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="8550" class="Symbol">}}</a>
    <a id="8557" class="Symbol">}</a>
</pre>{% endraw %}The result can be viewed as a generalisation of currying.  Indeed, the code to
establish the isomorphism is identical to what we wrote when discussing
[implication]({{ site.baseurl }}/Connectives/#implication).

#### Exercise `∃-distrib-⊎` (recommended)

Show that existentials distribute over disjunction:
{% raw %}<pre class="Agda"><a id="8874" class="Keyword">postulate</a>
  <a id="∃-distrib-⊎"></a><a id="8886" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#8886" class="Postulate">∃-distrib-⊎</a> <a id="8898" class="Symbol">:</a> <a id="8900" class="Symbol">∀</a> <a id="8902" class="Symbol">{</a><a id="8903" href="plfa.part1.Quantifiers.html#8903" class="Bound">A</a> <a id="8905" class="Symbol">:</a> <a id="8907" class="PrimitiveType">Set</a><a id="8910" class="Symbol">}</a> <a id="8912" class="Symbol">{</a><a id="8913" href="plfa.part1.Quantifiers.html#8913" class="Bound">B</a> <a id="8915" href="plfa.part1.Quantifiers.html#8915" class="Bound">C</a> <a id="8917" class="Symbol">:</a> <a id="8919" href="plfa.part1.Quantifiers.html#8903" class="Bound">A</a> <a id="8921" class="Symbol">→</a> <a id="8923" class="PrimitiveType">Set</a><a id="8926" class="Symbol">}</a> <a id="8928" class="Symbol">→</a>
    <a id="8934" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#7283" class="Function">∃[</a> <a id="8937" href="plfa.part1.Quantifiers.html#8937" class="Bound">x</a> <a id="8939" href="plfa.part1.Quantifiers.html#7283" class="Function">]</a> <a id="8941" class="Symbol">(</a><a id="8942" href="plfa.part1.Quantifiers.html#8913" class="Bound">B</a> <a id="8944" href="plfa.part1.Quantifiers.html#8937" class="Bound">x</a> <a id="8946" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#612" class="Datatype Operator">⊎</a> <a id="8948" href="plfa.part1.Quantifiers.html#8915" class="Bound">C</a> <a id="8950" href="plfa.part1.Quantifiers.html#8937" class="Bound">x</a><a id="8951" class="Symbol">)</a> <a id="8953" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#4365" class="Record Operator">≃</a> <a id="8955" class="Symbol">(</a><a id="8956" href="plfa.part1.Quantifiers.html#7283" class="Function">∃[</a> <a id="8959" href="plfa.part1.Quantifiers.html#8959" class="Bound">x</a> <a id="8961" href="plfa.part1.Quantifiers.html#7283" class="Function">]</a> <a id="8963" href="plfa.part1.Quantifiers.html#8913" class="Bound">B</a> <a id="8965" href="plfa.part1.Quantifiers.html#8959" class="Bound">x</a><a id="8966" class="Symbol">)</a> <a id="8968" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#612" class="Datatype Operator">⊎</a> <a id="8970" class="Symbol">(</a><a id="8971" href="plfa.part1.Quantifiers.html#7283" class="Function">∃[</a> <a id="8974" href="plfa.part1.Quantifiers.html#8974" class="Bound">x</a> <a id="8976" href="plfa.part1.Quantifiers.html#7283" class="Function">]</a> <a id="8978" href="plfa.part1.Quantifiers.html#8915" class="Bound">C</a> <a id="8980" href="plfa.part1.Quantifiers.html#8974" class="Bound">x</a><a id="8981" class="Symbol">)</a>
</pre>{% endraw %}
#### Exercise `∃×-implies-×∃` (practice)

Show that an existential of conjunctions implies a conjunction of existentials:
{% raw %}<pre class="Agda"><a id="9114" class="Keyword">postulate</a>
  <a id="∃×-implies-×∃"></a><a id="9126" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#9126" class="Postulate">∃×-implies-×∃</a> <a id="9140" class="Symbol">:</a> <a id="9142" class="Symbol">∀</a> <a id="9144" class="Symbol">{</a><a id="9145" href="plfa.part1.Quantifiers.html#9145" class="Bound">A</a> <a id="9147" class="Symbol">:</a> <a id="9149" class="PrimitiveType">Set</a><a id="9152" class="Symbol">}</a> <a id="9154" class="Symbol">{</a><a id="9155" href="plfa.part1.Quantifiers.html#9155" class="Bound">B</a> <a id="9157" href="plfa.part1.Quantifiers.html#9157" class="Bound">C</a> <a id="9159" class="Symbol">:</a> <a id="9161" href="plfa.part1.Quantifiers.html#9145" class="Bound">A</a> <a id="9163" class="Symbol">→</a> <a id="9165" class="PrimitiveType">Set</a><a id="9168" class="Symbol">}</a> <a id="9170" class="Symbol">→</a>
    <a id="9176" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#7283" class="Function">∃[</a> <a id="9179" href="plfa.part1.Quantifiers.html#9179" class="Bound">x</a> <a id="9181" href="plfa.part1.Quantifiers.html#7283" class="Function">]</a> <a id="9183" class="Symbol">(</a><a id="9184" href="plfa.part1.Quantifiers.html#9155" class="Bound">B</a> <a id="9186" href="plfa.part1.Quantifiers.html#9179" class="Bound">x</a> <a id="9188" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1162" class="Function Operator">×</a> <a id="9190" href="plfa.part1.Quantifiers.html#9157" class="Bound">C</a> <a id="9192" href="plfa.part1.Quantifiers.html#9179" class="Bound">x</a><a id="9193" class="Symbol">)</a> <a id="9195" class="Symbol">→</a> <a id="9197" class="Symbol">(</a><a id="9198" href="plfa.part1.Quantifiers.html#7283" class="Function">∃[</a> <a id="9201" href="plfa.part1.Quantifiers.html#9201" class="Bound">x</a> <a id="9203" href="plfa.part1.Quantifiers.html#7283" class="Function">]</a> <a id="9205" href="plfa.part1.Quantifiers.html#9155" class="Bound">B</a> <a id="9207" href="plfa.part1.Quantifiers.html#9201" class="Bound">x</a><a id="9208" class="Symbol">)</a> <a id="9210" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1162" class="Function Operator">×</a> <a id="9212" class="Symbol">(</a><a id="9213" href="plfa.part1.Quantifiers.html#7283" class="Function">∃[</a> <a id="9216" href="plfa.part1.Quantifiers.html#9216" class="Bound">x</a> <a id="9218" href="plfa.part1.Quantifiers.html#7283" class="Function">]</a> <a id="9220" href="plfa.part1.Quantifiers.html#9157" class="Bound">C</a> <a id="9222" href="plfa.part1.Quantifiers.html#9216" class="Bound">x</a><a id="9223" class="Symbol">)</a>
</pre>{% endraw %}Does the converse hold? If so, prove; if not, explain why.

#### Exercise `∃-⊎` (practice)

Let `Tri` and `B` be as in Exercise `∀-×`.
Show that `∃[ x ] B x` is isomorphic to `B aa ⊎ B bb ⊎ B cc`.


## An existential example

Recall the definitions of `even` and `odd` from
Chapter [Relations]({{ site.baseurl }}/Relations/):
{% raw %}<pre class="Agda"><a id="9559" class="Keyword">data</a> <a id="even"></a><a id="9564" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#9564" class="Datatype">even</a> <a id="9569" class="Symbol">:</a> <a id="9571" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a> <a id="9573" class="Symbol">→</a> <a id="9575" class="PrimitiveType">Set</a>
<a id="9579" class="Keyword">data</a> <a id="odd"></a><a id="9584" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#9584" class="Datatype">odd</a>  <a id="9589" class="Symbol">:</a> <a id="9591" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a> <a id="9593" class="Symbol">→</a> <a id="9595" class="PrimitiveType">Set</a>

<a id="9600" class="Keyword">data</a> <a id="9605" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#9564" class="Datatype">even</a> <a id="9610" class="Keyword">where</a>

  <a id="even.even-zero"></a><a id="9619" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#9619" class="InductiveConstructor">even-zero</a> <a id="9629" class="Symbol">:</a> <a id="9631" href="plfa.part1.Quantifiers.html#9564" class="Datatype">even</a> <a id="9636" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a>

  <a id="even.even-suc"></a><a id="9644" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#9644" class="InductiveConstructor">even-suc</a> <a id="9653" class="Symbol">:</a> <a id="9655" class="Symbol">∀</a> <a id="9657" class="Symbol">{</a><a id="9658" href="plfa.part1.Quantifiers.html#9658" class="Bound">n</a> <a id="9660" class="Symbol">:</a> <a id="9662" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="9663" class="Symbol">}</a>
    <a id="9669" class="Symbol">→</a> <a id="9671" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#9584" class="Datatype">odd</a> <a id="9675" href="plfa.part1.Quantifiers.html#9658" class="Bound">n</a>
      <a id="9683" class="Comment">------------</a>
    <a id="9700" class="Symbol">→</a> <a id="9702" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#9564" class="Datatype">even</a> <a id="9707" class="Symbol">(</a><a id="9708" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="9712" href="plfa.part1.Quantifiers.html#9658" class="Bound">n</a><a id="9713" class="Symbol">)</a>

<a id="9716" class="Keyword">data</a> <a id="9721" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#9584" class="Datatype">odd</a> <a id="9725" class="Keyword">where</a>
  <a id="odd.odd-suc"></a><a id="9733" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#9733" class="InductiveConstructor">odd-suc</a> <a id="9741" class="Symbol">:</a> <a id="9743" class="Symbol">∀</a> <a id="9745" class="Symbol">{</a><a id="9746" href="plfa.part1.Quantifiers.html#9746" class="Bound">n</a> <a id="9748" class="Symbol">:</a> <a id="9750" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="9751" class="Symbol">}</a>
    <a id="9757" class="Symbol">→</a> <a id="9759" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#9564" class="Datatype">even</a> <a id="9764" href="plfa.part1.Quantifiers.html#9746" class="Bound">n</a>
      <a id="9772" class="Comment">-----------</a>
    <a id="9788" class="Symbol">→</a> <a id="9790" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#9584" class="Datatype">odd</a> <a id="9794" class="Symbol">(</a><a id="9795" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="9799" href="plfa.part1.Quantifiers.html#9746" class="Bound">n</a><a id="9800" class="Symbol">)</a>
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
{% raw %}<pre class="Agda"><a id="even-∃"></a><a id="10421" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#10421" class="Function">even-∃</a> <a id="10428" class="Symbol">:</a> <a id="10430" class="Symbol">∀</a> <a id="10432" class="Symbol">{</a><a id="10433" href="plfa.part1.Quantifiers.html#10433" class="Bound">n</a> <a id="10435" class="Symbol">:</a> <a id="10437" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="10438" class="Symbol">}</a> <a id="10440" class="Symbol">→</a> <a id="10442" href="plfa.part1.Quantifiers.html#9564" class="Datatype">even</a> <a id="10447" href="plfa.part1.Quantifiers.html#10433" class="Bound">n</a> <a id="10449" class="Symbol">→</a> <a id="10451" href="plfa.part1.Quantifiers.html#7283" class="Function">∃[</a> <a id="10454" href="plfa.part1.Quantifiers.html#10454" class="Bound">m</a> <a id="10456" href="plfa.part1.Quantifiers.html#7283" class="Function">]</a> <a id="10458" class="Symbol">(</a>    <a id="10463" href="plfa.part1.Quantifiers.html#10454" class="Bound">m</a> <a id="10465" href="Agda.Builtin.Nat.html#501" class="Primitive Operator">*</a> <a id="10467" class="Number">2</a> <a id="10469" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="10471" href="plfa.part1.Quantifiers.html#10433" class="Bound">n</a><a id="10472" class="Symbol">)</a>
<a id="odd-∃"></a><a id="10474" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#10474" class="Function">odd-∃</a>  <a id="10481" class="Symbol">:</a> <a id="10483" class="Symbol">∀</a> <a id="10485" class="Symbol">{</a><a id="10486" href="plfa.part1.Quantifiers.html#10486" class="Bound">n</a> <a id="10488" class="Symbol">:</a> <a id="10490" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="10491" class="Symbol">}</a> <a id="10493" class="Symbol">→</a>  <a id="10496" href="plfa.part1.Quantifiers.html#9584" class="Datatype">odd</a> <a id="10500" href="plfa.part1.Quantifiers.html#10486" class="Bound">n</a> <a id="10502" class="Symbol">→</a> <a id="10504" href="plfa.part1.Quantifiers.html#7283" class="Function">∃[</a> <a id="10507" href="plfa.part1.Quantifiers.html#10507" class="Bound">m</a> <a id="10509" href="plfa.part1.Quantifiers.html#7283" class="Function">]</a> <a id="10511" class="Symbol">(</a><a id="10512" class="Number">1</a> <a id="10514" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="10516" href="plfa.part1.Quantifiers.html#10507" class="Bound">m</a> <a id="10518" href="Agda.Builtin.Nat.html#501" class="Primitive Operator">*</a> <a id="10520" class="Number">2</a> <a id="10522" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="10524" href="plfa.part1.Quantifiers.html#10486" class="Bound">n</a><a id="10525" class="Symbol">)</a>

<a id="10528" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#10421" class="Function">even-∃</a> <a id="10535" href="plfa.part1.Quantifiers.html#9619" class="InductiveConstructor">even-zero</a>                       <a id="10567" class="Symbol">=</a>  <a id="10570" href="plfa.part1.Quantifiers.html#4902" class="InductiveConstructor Operator">⟨</a> <a id="10572" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a> <a id="10577" href="plfa.part1.Quantifiers.html#4902" class="InductiveConstructor Operator">,</a> <a id="10579" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="10584" href="plfa.part1.Quantifiers.html#4902" class="InductiveConstructor Operator">⟩</a>
<a id="10586" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#10421" class="Function">even-∃</a> <a id="10593" class="Symbol">(</a><a id="10594" href="plfa.part1.Quantifiers.html#9644" class="InductiveConstructor">even-suc</a> <a id="10603" href="plfa.part1.Quantifiers.html#10603" class="Bound">o</a><a id="10604" class="Symbol">)</a> <a id="10606" class="Keyword">with</a> <a id="10611" href="plfa.part1.Quantifiers.html#10474" class="Function">odd-∃</a> <a id="10617" href="plfa.part1.Quantifiers.html#10603" class="Bound">o</a>
<a id="10619" class="Symbol">...</a>                    <a id="10642" class="Symbol">|</a> <a id="10644" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#4902" class="InductiveConstructor Operator">⟨</a> <a id="10646" href="plfa.part1.Quantifiers.html#10646" class="Bound">m</a> <a id="10648" href="plfa.part1.Quantifiers.html#4902" class="InductiveConstructor Operator">,</a> <a id="10650" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="10655" href="plfa.part1.Quantifiers.html#4902" class="InductiveConstructor Operator">⟩</a>  <a id="10658" class="Symbol">=</a>  <a id="10661" href="plfa.part1.Quantifiers.html#4902" class="InductiveConstructor Operator">⟨</a> <a id="10663" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="10667" href="plfa.part1.Quantifiers.html#10646" class="Bound">m</a> <a id="10669" href="plfa.part1.Quantifiers.html#4902" class="InductiveConstructor Operator">,</a> <a id="10671" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="10676" href="plfa.part1.Quantifiers.html#4902" class="InductiveConstructor Operator">⟩</a>

<a id="10679" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#10474" class="Function">odd-∃</a>  <a id="10686" class="Symbol">(</a><a id="10687" href="plfa.part1.Quantifiers.html#9733" class="InductiveConstructor">odd-suc</a> <a id="10695" href="plfa.part1.Quantifiers.html#10695" class="Bound">e</a><a id="10696" class="Symbol">)</a>  <a id="10699" class="Keyword">with</a> <a id="10704" href="plfa.part1.Quantifiers.html#10421" class="Function">even-∃</a> <a id="10711" href="plfa.part1.Quantifiers.html#10695" class="Bound">e</a>
<a id="10713" class="Symbol">...</a>                    <a id="10736" class="Symbol">|</a> <a id="10738" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#4902" class="InductiveConstructor Operator">⟨</a> <a id="10740" href="plfa.part1.Quantifiers.html#10740" class="Bound">m</a> <a id="10742" href="plfa.part1.Quantifiers.html#4902" class="InductiveConstructor Operator">,</a> <a id="10744" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="10749" href="plfa.part1.Quantifiers.html#4902" class="InductiveConstructor Operator">⟩</a>  <a id="10752" class="Symbol">=</a>  <a id="10755" href="plfa.part1.Quantifiers.html#4902" class="InductiveConstructor Operator">⟨</a> <a id="10757" href="plfa.part1.Quantifiers.html#10740" class="Bound">m</a> <a id="10759" href="plfa.part1.Quantifiers.html#4902" class="InductiveConstructor Operator">,</a> <a id="10761" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="10766" href="plfa.part1.Quantifiers.html#4902" class="InductiveConstructor Operator">⟩</a>
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
{% raw %}<pre class="Agda"><a id="∃-even"></a><a id="11786" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#11786" class="Function">∃-even</a> <a id="11793" class="Symbol">:</a> <a id="11795" class="Symbol">∀</a> <a id="11797" class="Symbol">{</a><a id="11798" href="plfa.part1.Quantifiers.html#11798" class="Bound">n</a> <a id="11800" class="Symbol">:</a> <a id="11802" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="11803" class="Symbol">}</a> <a id="11805" class="Symbol">→</a> <a id="11807" href="plfa.part1.Quantifiers.html#7283" class="Function">∃[</a> <a id="11810" href="plfa.part1.Quantifiers.html#11810" class="Bound">m</a> <a id="11812" href="plfa.part1.Quantifiers.html#7283" class="Function">]</a> <a id="11814" class="Symbol">(</a>    <a id="11819" href="plfa.part1.Quantifiers.html#11810" class="Bound">m</a> <a id="11821" href="Agda.Builtin.Nat.html#501" class="Primitive Operator">*</a> <a id="11823" class="Number">2</a> <a id="11825" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="11827" href="plfa.part1.Quantifiers.html#11798" class="Bound">n</a><a id="11828" class="Symbol">)</a> <a id="11830" class="Symbol">→</a> <a id="11832" href="plfa.part1.Quantifiers.html#9564" class="Datatype">even</a> <a id="11837" href="plfa.part1.Quantifiers.html#11798" class="Bound">n</a>
<a id="∃-odd"></a><a id="11839" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#11839" class="Function">∃-odd</a>  <a id="11846" class="Symbol">:</a> <a id="11848" class="Symbol">∀</a> <a id="11850" class="Symbol">{</a><a id="11851" href="plfa.part1.Quantifiers.html#11851" class="Bound">n</a> <a id="11853" class="Symbol">:</a> <a id="11855" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="11856" class="Symbol">}</a> <a id="11858" class="Symbol">→</a> <a id="11860" href="plfa.part1.Quantifiers.html#7283" class="Function">∃[</a> <a id="11863" href="plfa.part1.Quantifiers.html#11863" class="Bound">m</a> <a id="11865" href="plfa.part1.Quantifiers.html#7283" class="Function">]</a> <a id="11867" class="Symbol">(</a><a id="11868" class="Number">1</a> <a id="11870" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="11872" href="plfa.part1.Quantifiers.html#11863" class="Bound">m</a> <a id="11874" href="Agda.Builtin.Nat.html#501" class="Primitive Operator">*</a> <a id="11876" class="Number">2</a> <a id="11878" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="11880" href="plfa.part1.Quantifiers.html#11851" class="Bound">n</a><a id="11881" class="Symbol">)</a> <a id="11883" class="Symbol">→</a>  <a id="11886" href="plfa.part1.Quantifiers.html#9584" class="Datatype">odd</a> <a id="11890" href="plfa.part1.Quantifiers.html#11851" class="Bound">n</a>

<a id="11893" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#11786" class="Function">∃-even</a> <a id="11900" href="plfa.part1.Quantifiers.html#4902" class="InductiveConstructor Operator">⟨</a>  <a id="11903" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a> <a id="11908" href="plfa.part1.Quantifiers.html#4902" class="InductiveConstructor Operator">,</a> <a id="11910" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="11915" href="plfa.part1.Quantifiers.html#4902" class="InductiveConstructor Operator">⟩</a>  <a id="11918" class="Symbol">=</a>  <a id="11921" href="plfa.part1.Quantifiers.html#9619" class="InductiveConstructor">even-zero</a>
<a id="11931" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#11786" class="Function">∃-even</a> <a id="11938" href="plfa.part1.Quantifiers.html#4902" class="InductiveConstructor Operator">⟨</a> <a id="11940" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="11944" href="plfa.part1.Quantifiers.html#11944" class="Bound">m</a> <a id="11946" href="plfa.part1.Quantifiers.html#4902" class="InductiveConstructor Operator">,</a> <a id="11948" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="11953" href="plfa.part1.Quantifiers.html#4902" class="InductiveConstructor Operator">⟩</a>  <a id="11956" class="Symbol">=</a>  <a id="11959" href="plfa.part1.Quantifiers.html#9644" class="InductiveConstructor">even-suc</a> <a id="11968" class="Symbol">(</a><a id="11969" href="plfa.part1.Quantifiers.html#11839" class="Function">∃-odd</a> <a id="11975" href="plfa.part1.Quantifiers.html#4902" class="InductiveConstructor Operator">⟨</a> <a id="11977" href="plfa.part1.Quantifiers.html#11944" class="Bound">m</a> <a id="11979" href="plfa.part1.Quantifiers.html#4902" class="InductiveConstructor Operator">,</a> <a id="11981" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="11986" href="plfa.part1.Quantifiers.html#4902" class="InductiveConstructor Operator">⟩</a><a id="11987" class="Symbol">)</a>

<a id="11990" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#11839" class="Function">∃-odd</a>  <a id="11997" href="plfa.part1.Quantifiers.html#4902" class="InductiveConstructor Operator">⟨</a>     <a id="12003" href="plfa.part1.Quantifiers.html#12003" class="Bound">m</a> <a id="12005" href="plfa.part1.Quantifiers.html#4902" class="InductiveConstructor Operator">,</a> <a id="12007" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="12012" href="plfa.part1.Quantifiers.html#4902" class="InductiveConstructor Operator">⟩</a>  <a id="12015" class="Symbol">=</a>  <a id="12018" href="plfa.part1.Quantifiers.html#9733" class="InductiveConstructor">odd-suc</a> <a id="12026" class="Symbol">(</a><a id="12027" href="plfa.part1.Quantifiers.html#11786" class="Function">∃-even</a> <a id="12034" href="plfa.part1.Quantifiers.html#4902" class="InductiveConstructor Operator">⟨</a> <a id="12036" href="plfa.part1.Quantifiers.html#12003" class="Bound">m</a> <a id="12038" href="plfa.part1.Quantifiers.html#4902" class="InductiveConstructor Operator">,</a> <a id="12040" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="12045" href="plfa.part1.Quantifiers.html#4902" class="InductiveConstructor Operator">⟩</a><a id="12046" class="Symbol">)</a>
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

{% raw %}<pre class="Agda"><a id="13051" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}
#### Exercise `∃-+-≤` (practice)

Show that `y ≤ z` holds if and only if there exists a `x` such that
`x + y ≡ z`.

{% raw %}<pre class="Agda"><a id="13199" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}

## Existentials, Universals, and Negation

Negation of an existential is isomorphic to the universal
of a negation.  Considering that existentials are generalised
disjunction and universals are generalised conjunction, this
result is analogous to the one which tells us that negation
of a disjunction is isomorphic to a conjunction of negations:
{% raw %}<pre class="Agda"><a id="¬∃≃∀¬"></a><a id="13578" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#13578" class="Function">¬∃≃∀¬</a> <a id="13584" class="Symbol">:</a> <a id="13586" class="Symbol">∀</a> <a id="13588" class="Symbol">{</a><a id="13589" href="plfa.part1.Quantifiers.html#13589" class="Bound">A</a> <a id="13591" class="Symbol">:</a> <a id="13593" class="PrimitiveType">Set</a><a id="13596" class="Symbol">}</a> <a id="13598" class="Symbol">{</a><a id="13599" href="plfa.part1.Quantifiers.html#13599" class="Bound">B</a> <a id="13601" class="Symbol">:</a> <a id="13603" href="plfa.part1.Quantifiers.html#13589" class="Bound">A</a> <a id="13605" class="Symbol">→</a> <a id="13607" class="PrimitiveType">Set</a><a id="13610" class="Symbol">}</a>
  <a id="13614" class="Symbol">→</a> <a id="13616" class="Symbol">(</a><a id="13617" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#535" class="Function Operator">¬</a> <a id="13619" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#7283" class="Function">∃[</a> <a id="13622" href="plfa.part1.Quantifiers.html#13622" class="Bound">x</a> <a id="13624" href="plfa.part1.Quantifiers.html#7283" class="Function">]</a> <a id="13626" href="plfa.part1.Quantifiers.html#13599" class="Bound">B</a> <a id="13628" href="plfa.part1.Quantifiers.html#13622" class="Bound">x</a><a id="13629" class="Symbol">)</a> <a id="13631" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#4365" class="Record Operator">≃</a> <a id="13633" class="Symbol">∀</a> <a id="13635" href="plfa.part1.Quantifiers.html#13635" class="Bound">x</a> <a id="13637" class="Symbol">→</a> <a id="13639" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#535" class="Function Operator">¬</a> <a id="13641" href="plfa.part1.Quantifiers.html#13599" class="Bound">B</a> <a id="13643" href="plfa.part1.Quantifiers.html#13635" class="Bound">x</a>
<a id="13645" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#13578" class="Function">¬∃≃∀¬</a> <a id="13651" class="Symbol">=</a>
  <a id="13655" class="Keyword">record</a>
    <a id="13666" class="Symbol">{</a> <a id="13668" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#4405" class="Field">to</a>      <a id="13676" class="Symbol">=</a>  <a id="13679" class="Symbol">λ{</a> <a id="13682" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#13682" class="Bound">¬∃xy</a> <a id="13687" href="plfa.part1.Quantifiers.html#13687" class="Bound">x</a> <a id="13689" href="plfa.part1.Quantifiers.html#13689" class="Bound">y</a> <a id="13691" class="Symbol">→</a> <a id="13693" href="plfa.part1.Quantifiers.html#13682" class="Bound">¬∃xy</a> <a id="13698" href="plfa.part1.Quantifiers.html#4902" class="InductiveConstructor Operator">⟨</a> <a id="13700" href="plfa.part1.Quantifiers.html#13687" class="Bound">x</a> <a id="13702" href="plfa.part1.Quantifiers.html#4902" class="InductiveConstructor Operator">,</a> <a id="13704" href="plfa.part1.Quantifiers.html#13689" class="Bound">y</a> <a id="13706" href="plfa.part1.Quantifiers.html#4902" class="InductiveConstructor Operator">⟩</a> <a id="13708" class="Symbol">}</a>
    <a id="13714" class="Symbol">;</a> <a id="13716" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#4422" class="Field">from</a>    <a id="13724" class="Symbol">=</a>  <a id="13727" class="Symbol">λ{</a> <a id="13730" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#13730" class="Bound">∀¬xy</a> <a id="13735" href="plfa.part1.Quantifiers.html#4902" class="InductiveConstructor Operator">⟨</a> <a id="13737" href="plfa.part1.Quantifiers.html#13737" class="Bound">x</a> <a id="13739" href="plfa.part1.Quantifiers.html#4902" class="InductiveConstructor Operator">,</a> <a id="13741" href="plfa.part1.Quantifiers.html#13741" class="Bound">y</a> <a id="13743" href="plfa.part1.Quantifiers.html#4902" class="InductiveConstructor Operator">⟩</a> <a id="13745" class="Symbol">→</a> <a id="13747" href="plfa.part1.Quantifiers.html#13730" class="Bound">∀¬xy</a> <a id="13752" href="plfa.part1.Quantifiers.html#13737" class="Bound">x</a> <a id="13754" href="plfa.part1.Quantifiers.html#13741" class="Bound">y</a> <a id="13756" class="Symbol">}</a>
    <a id="13762" class="Symbol">;</a> <a id="13764" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#4439" class="Field">from∘to</a> <a id="13772" class="Symbol">=</a>  <a id="13775" class="Symbol">λ{</a> <a id="13778" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#13778" class="Bound">¬∃xy</a> <a id="13783" class="Symbol">→</a> <a id="13785" href="plfa.part1.Isomorphism.html#2684" class="Postulate">extensionality</a> <a id="13800" class="Symbol">λ{</a> <a id="13803" href="plfa.part1.Quantifiers.html#4902" class="InductiveConstructor Operator">⟨</a> <a id="13805" href="plfa.part1.Quantifiers.html#13805" class="Bound">x</a> <a id="13807" href="plfa.part1.Quantifiers.html#4902" class="InductiveConstructor Operator">,</a> <a id="13809" href="plfa.part1.Quantifiers.html#13809" class="Bound">y</a> <a id="13811" href="plfa.part1.Quantifiers.html#4902" class="InductiveConstructor Operator">⟩</a> <a id="13813" class="Symbol">→</a> <a id="13815" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="13820" class="Symbol">}</a> <a id="13822" class="Symbol">}</a>
    <a id="13828" class="Symbol">;</a> <a id="13830" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#4481" class="Field">to∘from</a> <a id="13838" class="Symbol">=</a>  <a id="13841" class="Symbol">λ{</a> <a id="13844" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#13844" class="Bound">∀¬xy</a> <a id="13849" class="Symbol">→</a> <a id="13851" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="13856" class="Symbol">}</a>
    <a id="13862" class="Symbol">}</a>
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
{% raw %}<pre class="Agda"><a id="14679" class="Keyword">postulate</a>
  <a id="∃¬-implies-¬∀"></a><a id="14691" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#14691" class="Postulate">∃¬-implies-¬∀</a> <a id="14705" class="Symbol">:</a> <a id="14707" class="Symbol">∀</a> <a id="14709" class="Symbol">{</a><a id="14710" href="plfa.part1.Quantifiers.html#14710" class="Bound">A</a> <a id="14712" class="Symbol">:</a> <a id="14714" class="PrimitiveType">Set</a><a id="14717" class="Symbol">}</a> <a id="14719" class="Symbol">{</a><a id="14720" href="plfa.part1.Quantifiers.html#14720" class="Bound">B</a> <a id="14722" class="Symbol">:</a> <a id="14724" href="plfa.part1.Quantifiers.html#14710" class="Bound">A</a> <a id="14726" class="Symbol">→</a> <a id="14728" class="PrimitiveType">Set</a><a id="14731" class="Symbol">}</a>
    <a id="14737" class="Symbol">→</a> <a id="14739" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#7283" class="Function">∃[</a> <a id="14742" href="plfa.part1.Quantifiers.html#14742" class="Bound">x</a> <a id="14744" href="plfa.part1.Quantifiers.html#7283" class="Function">]</a> <a id="14746" class="Symbol">(</a><a id="14747" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#535" class="Function Operator">¬</a> <a id="14749" href="plfa.part1.Quantifiers.html#14720" class="Bound">B</a> <a id="14751" href="plfa.part1.Quantifiers.html#14742" class="Bound">x</a><a id="14752" class="Symbol">)</a>
      <a id="14760" class="Comment">--------------</a>
    <a id="14779" class="Symbol">→</a> <a id="14781" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#535" class="Function Operator">¬</a> <a id="14783" class="Symbol">(∀</a> <a id="14786" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Quantifiers.md %}{% raw %}#14786" class="Bound">x</a> <a id="14788" class="Symbol">→</a> <a id="14790" href="plfa.part1.Quantifiers.html#14720" class="Bound">B</a> <a id="14792" href="plfa.part1.Quantifiers.html#14786" class="Bound">x</a><a id="14793" class="Symbol">)</a>
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

{% raw %}<pre class="Agda"><a id="16057" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}

## Standard library

Definitions similar to those in this chapter can be found in the standard library:
{% raw %}<pre class="Agda"><a id="16194" class="Keyword">import</a> <a id="16201" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html" class="Module">Data.Product</a> <a id="16214" class="Keyword">using</a> <a id="16220" class="Symbol">(</a><a id="16221" href="Agda.Builtin.Sigma.html#139" class="Record">Σ</a><a id="16222" class="Symbol">;</a> <a id="16224" href="Agda.Builtin.Sigma.html#209" class="InductiveConstructor Operator">_,_</a><a id="16227" class="Symbol">;</a> <a id="16229" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1364" class="Function">∃</a><a id="16230" class="Symbol">;</a> <a id="16232" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#911" class="Function">Σ-syntax</a><a id="16240" class="Symbol">;</a> <a id="16242" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1783" class="Function">∃-syntax</a><a id="16250" class="Symbol">)</a>
</pre>{% endraw %}

## Unicode

This chapter uses the following unicode:

    Π  U+03A0  GREEK CAPITAL LETTER PI (\Pi)
    Σ  U+03A3  GREEK CAPITAL LETTER SIGMA (\Sigma)
    ∃  U+2203  THERE EXISTS (\ex, \exists)
