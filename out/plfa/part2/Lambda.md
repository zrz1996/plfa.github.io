---
src       : "src/plfa/part2/Lambda.lagda.md"
title     : "Lambda: Introduction to Lambda Calculus"
layout    : page
prev      : /Lists/
permalink : /Lambda/
next      : /Properties/
---

{% raw %}<pre class="Agda"><a id="151" class="Keyword">module</a> <a id="158" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}" class="Module">plfa.part2.Lambda</a> <a id="176" class="Keyword">where</a>
</pre>{% endraw %}
The _lambda-calculus_, first published by the logician Alonzo Church in
1932, is a core calculus with only three syntactic constructs:
variables, abstraction, and application.  It captures the key concept of
_functional abstraction_, which appears in pretty much every programming
language, in the form of either functions, procedures, or methods.
The _simply-typed lambda calculus_ (or STLC) is a variant of the
lambda calculus published by Church in 1940.  It has the three
constructs above for function types, plus whatever else is required
for base types. Church had a minimal base type with no operations.
We will instead echo Plotkin's _Programmable Computable
Functions_ (PCF), and add operations on natural numbers and
recursive function definitions.

This chapter formalises the simply-typed lambda calculus, giving its
syntax, small-step semantics, and typing rules.  The next chapter
[Properties]({{ site.baseurl }}/Properties/)
proves its main properties, including
progress and preservation.  Following chapters will look at a number
of variants of lambda calculus.

Be aware that the approach we take here is _not_ our recommended
approach to formalisation.  Using de Bruijn indices and
inherently-typed terms, as we will do in
Chapter [DeBruijn]({{ site.baseurl }}/DeBruijn/),
leads to a more compact formulation.  Nonetheless, we begin with named
variables, partly because such terms are easier to read and partly
because the development is more traditional.

The development in this chapter was inspired by the corresponding
development in Chapter _Stlc_ of _Software Foundations_
(_Programming Language Foundations_).  We differ by
representing contexts explicitly (as lists pairing identifiers with
types) rather than as partial maps (which take identifiers to types),
which corresponds better to our subsequent development of DeBruijn
notation. We also differ by taking natural numbers as the base type
rather than booleans, allowing more sophisticated examples. In
particular, we will be able to show (twice!) that two plus two is
four.

## Imports

{% raw %}<pre class="Agda"><a id="2262" class="Keyword">open</a> <a id="2267" class="Keyword">import</a> <a id="2274" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.html" class="Module">Relation.Binary.PropositionalEquality</a> <a id="2312" class="Keyword">using</a> <a id="2318" class="Symbol">(</a><a id="2319" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">_≡_</a><a id="2322" class="Symbol">;</a> <a id="2324" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#799" class="Function Operator">_≢_</a><a id="2327" class="Symbol">;</a> <a id="2329" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a><a id="2333" class="Symbol">)</a>
<a id="2335" class="Keyword">open</a> <a id="2340" class="Keyword">import</a> <a id="2347" href="https://agda.github.io/agda-stdlib/v1.1/Data.String.html" class="Module">Data.String</a> <a id="2359" class="Keyword">using</a> <a id="2365" class="Symbol">(</a><a id="2366" href="Agda.Builtin.String.html#206" class="Postulate">String</a><a id="2372" class="Symbol">;</a> <a id="2374" href="https://agda.github.io/agda-stdlib/v1.1/Data.String.Properties.html#2569" class="Function Operator">_≟_</a><a id="2377" class="Symbol">)</a>
<a id="2379" class="Keyword">open</a> <a id="2384" class="Keyword">import</a> <a id="2391" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.html" class="Module">Data.Nat</a> <a id="2400" class="Keyword">using</a> <a id="2406" class="Symbol">(</a><a id="2407" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="2408" class="Symbol">;</a> <a id="2410" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a><a id="2414" class="Symbol">;</a> <a id="2416" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a><a id="2419" class="Symbol">)</a>
<a id="2421" class="Keyword">open</a> <a id="2426" class="Keyword">import</a> <a id="2433" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html" class="Module">Data.Empty</a> <a id="2444" class="Keyword">using</a> <a id="2450" class="Symbol">(</a><a id="2451" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html#279" class="Datatype">⊥</a><a id="2452" class="Symbol">;</a> <a id="2454" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html#294" class="Function">⊥-elim</a><a id="2460" class="Symbol">)</a>
<a id="2462" class="Keyword">open</a> <a id="2467" class="Keyword">import</a> <a id="2474" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html" class="Module">Relation.Nullary</a> <a id="2491" class="Keyword">using</a> <a id="2497" class="Symbol">(</a><a id="2498" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#605" class="Datatype">Dec</a><a id="2501" class="Symbol">;</a> <a id="2503" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#641" class="InductiveConstructor">yes</a><a id="2506" class="Symbol">;</a> <a id="2508" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#668" class="InductiveConstructor">no</a><a id="2510" class="Symbol">;</a> <a id="2512" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#535" class="Function Operator">¬_</a><a id="2514" class="Symbol">)</a>
<a id="2516" class="Keyword">open</a> <a id="2521" class="Keyword">import</a> <a id="2528" href="https://agda.github.io/agda-stdlib/v1.1/Data.List.html" class="Module">Data.List</a> <a id="2538" class="Keyword">using</a> <a id="2544" class="Symbol">(</a><a id="2545" href="Agda.Builtin.List.html#121" class="Datatype">List</a><a id="2549" class="Symbol">;</a> <a id="2551" href="Agda.Builtin.List.html#173" class="InductiveConstructor Operator">_∷_</a><a id="2554" class="Symbol">;</a> <a id="2556" href="https://agda.github.io/agda-stdlib/v1.1/Data.List.Base.html#8786" class="InductiveConstructor">[]</a><a id="2558" class="Symbol">)</a>
</pre>{% endraw %}
## Syntax of terms

Terms have seven constructs. Three are for the core lambda calculus:

  * Variables `` ` x ``
  * Abstractions `ƛ x ⇒ N`
  * Applications `L · M`

Three are for the naturals:

  * Zero `` `zero ``
  * Successor `` `suc ``
  * Case `` case L [zero⇒ M |suc x ⇒ N ] ``

And one is for recursion:

  * Fixpoint `μ x ⇒ M`

Abstraction is also called _lambda abstraction_, and is the construct
from which the calculus takes its name.

With the exception of variables and fixpoints, each term
form either constructs a value of a given type (abstractions yield functions,
zero and successor yield natural numbers) or deconstructs it (applications use functions,
case terms use naturals). We will see this again when we come
to the rules for assigning types to terms, where constructors
correspond to introduction rules and deconstructors to eliminators.

Here is the syntax of terms in Backus-Naur Form (BNF):

    L, M, N  ::=
      ` x  |  ƛ x ⇒ N  |  L · M  |
      `zero  |  `suc M  |  case L [zero⇒ M |suc x ⇒ N ]  |
      μ x ⇒ M

And here it is formalised in Agda:
{% raw %}<pre class="Agda"><a id="Id"></a><a id="3653" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3653" class="Function">Id</a> <a id="3656" class="Symbol">:</a> <a id="3658" class="PrimitiveType">Set</a>
<a id="3662" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3653" class="Function">Id</a> <a id="3665" class="Symbol">=</a> <a id="3667" href="Agda.Builtin.String.html#206" class="Postulate">String</a>

<a id="3675" class="Keyword">infix</a>  <a id="3682" class="Number">5</a>  <a id="3685" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3812" class="InductiveConstructor Operator">ƛ_⇒_</a>
<a id="3690" class="Keyword">infix</a>  <a id="3697" class="Number">5</a>  <a id="3700" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#4041" class="InductiveConstructor Operator">μ_⇒_</a>
<a id="3705" class="Keyword">infixl</a> <a id="3712" class="Number">7</a>  <a id="3715" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#33710" class="InductiveConstructor Operator">_·_</a>
<a id="3719" class="Keyword">infix</a>  <a id="3726" class="Number">8</a>  <a id="3729" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3940" class="InductiveConstructor Operator">`suc_</a>
<a id="3735" class="Keyword">infix</a>  <a id="3742" class="Number">9</a>  <a id="3745" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3773" class="InductiveConstructor Operator">`_</a>

<a id="3749" class="Keyword">data</a> <a id="Term"></a><a id="3754" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3754" class="Datatype">Term</a> <a id="3759" class="Symbol">:</a> <a id="3761" class="PrimitiveType">Set</a> <a id="3765" class="Keyword">where</a>
  <a id="Term.`_"></a><a id="3773" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3773" class="InductiveConstructor Operator">`_</a>                      <a id="3797" class="Symbol">:</a>  <a id="3800" href="plfa.part2.Lambda.html#3653" class="Function">Id</a> <a id="3803" class="Symbol">→</a> <a id="3805" href="plfa.part2.Lambda.html#3754" class="Datatype">Term</a>
  <a id="Term.ƛ_⇒_"></a><a id="3812" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3812" class="InductiveConstructor Operator">ƛ_⇒_</a>                    <a id="3836" class="Symbol">:</a>  <a id="3839" href="plfa.part2.Lambda.html#3653" class="Function">Id</a> <a id="3842" class="Symbol">→</a> <a id="3844" href="plfa.part2.Lambda.html#3754" class="Datatype">Term</a> <a id="3849" class="Symbol">→</a> <a id="3851" href="plfa.part2.Lambda.html#3754" class="Datatype">Term</a>
  <a id="Term._·_"></a><a id="3858" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3858" class="InductiveConstructor Operator">_·_</a>                     <a id="3882" class="Symbol">:</a>  <a id="3885" href="plfa.part2.Lambda.html#3754" class="Datatype">Term</a> <a id="3890" class="Symbol">→</a> <a id="3892" href="plfa.part2.Lambda.html#3754" class="Datatype">Term</a> <a id="3897" class="Symbol">→</a> <a id="3899" href="plfa.part2.Lambda.html#3754" class="Datatype">Term</a>
  <a id="Term.`zero"></a><a id="3906" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3906" class="InductiveConstructor">`zero</a>                   <a id="3930" class="Symbol">:</a>  <a id="3933" href="plfa.part2.Lambda.html#3754" class="Datatype">Term</a>
  <a id="Term.`suc_"></a><a id="3940" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3940" class="InductiveConstructor Operator">`suc_</a>                   <a id="3964" class="Symbol">:</a>  <a id="3967" href="plfa.part2.Lambda.html#3754" class="Datatype">Term</a> <a id="3972" class="Symbol">→</a> <a id="3974" href="plfa.part2.Lambda.html#3754" class="Datatype">Term</a>
  <a id="Term.case_[zero⇒_|suc_⇒_]"></a><a id="3981" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3981" class="InductiveConstructor Operator">case_[zero⇒_|suc_⇒_]</a>    <a id="4005" class="Symbol">:</a>  <a id="4008" href="plfa.part2.Lambda.html#3754" class="Datatype">Term</a> <a id="4013" class="Symbol">→</a> <a id="4015" href="plfa.part2.Lambda.html#3754" class="Datatype">Term</a> <a id="4020" class="Symbol">→</a> <a id="4022" href="plfa.part2.Lambda.html#3653" class="Function">Id</a> <a id="4025" class="Symbol">→</a> <a id="4027" href="plfa.part2.Lambda.html#3754" class="Datatype">Term</a> <a id="4032" class="Symbol">→</a> <a id="4034" href="plfa.part2.Lambda.html#3754" class="Datatype">Term</a>
  <a id="Term.μ_⇒_"></a><a id="4041" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#4041" class="InductiveConstructor Operator">μ_⇒_</a>                    <a id="4065" class="Symbol">:</a>  <a id="4068" href="plfa.part2.Lambda.html#3653" class="Function">Id</a> <a id="4071" class="Symbol">→</a> <a id="4073" href="plfa.part2.Lambda.html#3754" class="Datatype">Term</a> <a id="4078" class="Symbol">→</a> <a id="4080" href="plfa.part2.Lambda.html#3754" class="Datatype">Term</a>
</pre>{% endraw %}We represent identifiers by strings.  We choose precedence so that
lambda abstraction and fixpoint bind least tightly, then application,
then successor, and tightest of all is the constructor for variables.
Case expressions are self-bracketing.


### Example terms

Here are some example terms: the natural number two,
a function that adds naturals,
and a term that computes two plus two:
{% raw %}<pre class="Agda"><a id="two"></a><a id="4482" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#4482" class="Function">two</a> <a id="4486" class="Symbol">:</a> <a id="4488" href="plfa.part2.Lambda.html#3754" class="Datatype">Term</a>
<a id="4493" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#4482" class="Function">two</a> <a id="4497" class="Symbol">=</a> <a id="4499" href="plfa.part2.Lambda.html#3940" class="InductiveConstructor Operator">`suc</a> <a id="4504" href="plfa.part2.Lambda.html#3940" class="InductiveConstructor Operator">`suc</a> <a id="4509" href="plfa.part2.Lambda.html#3906" class="InductiveConstructor">`zero</a>

<a id="plus"></a><a id="4516" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#4516" class="Function">plus</a> <a id="4521" class="Symbol">:</a> <a id="4523" href="plfa.part2.Lambda.html#3754" class="Datatype">Term</a>
<a id="4528" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#4516" class="Function">plus</a> <a id="4533" class="Symbol">=</a> <a id="4535" href="plfa.part2.Lambda.html#4041" class="InductiveConstructor Operator">μ</a> <a id="4537" class="String">&quot;+&quot;</a> <a id="4541" href="plfa.part2.Lambda.html#4041" class="InductiveConstructor Operator">⇒</a> <a id="4543" href="plfa.part2.Lambda.html#3812" class="InductiveConstructor Operator">ƛ</a> <a id="4545" class="String">&quot;m&quot;</a> <a id="4549" href="plfa.part2.Lambda.html#3812" class="InductiveConstructor Operator">⇒</a> <a id="4551" href="plfa.part2.Lambda.html#3812" class="InductiveConstructor Operator">ƛ</a> <a id="4553" class="String">&quot;n&quot;</a> <a id="4557" href="plfa.part2.Lambda.html#3812" class="InductiveConstructor Operator">⇒</a>
         <a id="4568" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3981" class="InductiveConstructor Operator">case</a> <a id="4573" href="plfa.part2.Lambda.html#3773" class="InductiveConstructor Operator">`</a> <a id="4575" class="String">&quot;m&quot;</a>
           <a id="4590" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3981" class="InductiveConstructor Operator">[zero⇒</a> <a id="4597" href="plfa.part2.Lambda.html#3773" class="InductiveConstructor Operator">`</a> <a id="4599" class="String">&quot;n&quot;</a>
           <a id="4614" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3981" class="InductiveConstructor Operator">|suc</a> <a id="4619" class="String">&quot;m&quot;</a> <a id="4623" href="plfa.part2.Lambda.html#3981" class="InductiveConstructor Operator">⇒</a> <a id="4625" href="plfa.part2.Lambda.html#3940" class="InductiveConstructor Operator">`suc</a> <a id="4630" class="Symbol">(</a><a id="4631" href="plfa.part2.Lambda.html#3773" class="InductiveConstructor Operator">`</a> <a id="4633" class="String">&quot;+&quot;</a> <a id="4637" href="plfa.part2.Lambda.html#3858" class="InductiveConstructor Operator">·</a> <a id="4639" href="plfa.part2.Lambda.html#3773" class="InductiveConstructor Operator">`</a> <a id="4641" class="String">&quot;m&quot;</a> <a id="4645" href="plfa.part2.Lambda.html#3858" class="InductiveConstructor Operator">·</a> <a id="4647" href="plfa.part2.Lambda.html#3773" class="InductiveConstructor Operator">`</a> <a id="4649" class="String">&quot;n&quot;</a><a id="4652" class="Symbol">)</a> <a id="4654" href="plfa.part2.Lambda.html#3981" class="InductiveConstructor Operator">]</a>
</pre>{% endraw %}The recursive definition of addition is similar to our original
definition of `_+_` for naturals, as given in
Chapter [Naturals]({{ site.baseurl }}/Naturals/#plus).
Here variable "m" is bound twice, once in a lambda abstraction and once in
the successor branch of the case; the first use of "m" refers to
the former and the second to the latter.  Any use of "m" in the successor branch
must refer to the latter binding, and so we say that the latter binding _shadows_
the former.  Later we will confirm that two plus two is four, in other words that
the term

    plus · two · two

reduces to `` `suc `suc `suc `suc `zero ``.

As a second example, we use higher-order functions to represent
natural numbers.  In particular, the number _n_ is represented by a
function that accepts two arguments and applies the first _n_ times to the
second.  This is called the _Church representation_ of the
naturals.  Here are some example terms: the Church numeral two, a
function that adds Church numerals, a function to compute successor,
and a term that computes two plus two:
{% raw %}<pre class="Agda"><a id="twoᶜ"></a><a id="5731" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#5731" class="Function">twoᶜ</a> <a id="5736" class="Symbol">:</a> <a id="5738" href="plfa.part2.Lambda.html#3754" class="Datatype">Term</a>
<a id="5743" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#5731" class="Function">twoᶜ</a> <a id="5748" class="Symbol">=</a>  <a id="5751" href="plfa.part2.Lambda.html#3812" class="InductiveConstructor Operator">ƛ</a> <a id="5753" class="String">&quot;s&quot;</a> <a id="5757" href="plfa.part2.Lambda.html#3812" class="InductiveConstructor Operator">⇒</a> <a id="5759" href="plfa.part2.Lambda.html#3812" class="InductiveConstructor Operator">ƛ</a> <a id="5761" class="String">&quot;z&quot;</a> <a id="5765" href="plfa.part2.Lambda.html#3812" class="InductiveConstructor Operator">⇒</a> <a id="5767" href="plfa.part2.Lambda.html#3773" class="InductiveConstructor Operator">`</a> <a id="5769" class="String">&quot;s&quot;</a> <a id="5773" href="plfa.part2.Lambda.html#3858" class="InductiveConstructor Operator">·</a> <a id="5775" class="Symbol">(</a><a id="5776" href="plfa.part2.Lambda.html#3773" class="InductiveConstructor Operator">`</a> <a id="5778" class="String">&quot;s&quot;</a> <a id="5782" href="plfa.part2.Lambda.html#3858" class="InductiveConstructor Operator">·</a> <a id="5784" href="plfa.part2.Lambda.html#3773" class="InductiveConstructor Operator">`</a> <a id="5786" class="String">&quot;z&quot;</a><a id="5789" class="Symbol">)</a>

<a id="plusᶜ"></a><a id="5792" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#5792" class="Function">plusᶜ</a> <a id="5798" class="Symbol">:</a> <a id="5800" href="plfa.part2.Lambda.html#3754" class="Datatype">Term</a>
<a id="5805" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#5792" class="Function">plusᶜ</a> <a id="5811" class="Symbol">=</a>  <a id="5814" href="plfa.part2.Lambda.html#3812" class="InductiveConstructor Operator">ƛ</a> <a id="5816" class="String">&quot;m&quot;</a> <a id="5820" href="plfa.part2.Lambda.html#3812" class="InductiveConstructor Operator">⇒</a> <a id="5822" href="plfa.part2.Lambda.html#3812" class="InductiveConstructor Operator">ƛ</a> <a id="5824" class="String">&quot;n&quot;</a> <a id="5828" href="plfa.part2.Lambda.html#3812" class="InductiveConstructor Operator">⇒</a> <a id="5830" href="plfa.part2.Lambda.html#3812" class="InductiveConstructor Operator">ƛ</a> <a id="5832" class="String">&quot;s&quot;</a> <a id="5836" href="plfa.part2.Lambda.html#3812" class="InductiveConstructor Operator">⇒</a> <a id="5838" href="plfa.part2.Lambda.html#3812" class="InductiveConstructor Operator">ƛ</a> <a id="5840" class="String">&quot;z&quot;</a> <a id="5844" href="plfa.part2.Lambda.html#3812" class="InductiveConstructor Operator">⇒</a>
         <a id="5855" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3773" class="InductiveConstructor Operator">`</a> <a id="5857" class="String">&quot;m&quot;</a> <a id="5861" href="plfa.part2.Lambda.html#3858" class="InductiveConstructor Operator">·</a> <a id="5863" href="plfa.part2.Lambda.html#3773" class="InductiveConstructor Operator">`</a> <a id="5865" class="String">&quot;s&quot;</a> <a id="5869" href="plfa.part2.Lambda.html#3858" class="InductiveConstructor Operator">·</a> <a id="5871" class="Symbol">(</a><a id="5872" href="plfa.part2.Lambda.html#3773" class="InductiveConstructor Operator">`</a> <a id="5874" class="String">&quot;n&quot;</a> <a id="5878" href="plfa.part2.Lambda.html#3858" class="InductiveConstructor Operator">·</a> <a id="5880" href="plfa.part2.Lambda.html#3773" class="InductiveConstructor Operator">`</a> <a id="5882" class="String">&quot;s&quot;</a> <a id="5886" href="plfa.part2.Lambda.html#3858" class="InductiveConstructor Operator">·</a> <a id="5888" href="plfa.part2.Lambda.html#3773" class="InductiveConstructor Operator">`</a> <a id="5890" class="String">&quot;z&quot;</a><a id="5893" class="Symbol">)</a>

<a id="sucᶜ"></a><a id="5896" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#5896" class="Function">sucᶜ</a> <a id="5901" class="Symbol">:</a> <a id="5903" href="plfa.part2.Lambda.html#3754" class="Datatype">Term</a>
<a id="5908" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#5896" class="Function">sucᶜ</a> <a id="5913" class="Symbol">=</a> <a id="5915" href="plfa.part2.Lambda.html#3812" class="InductiveConstructor Operator">ƛ</a> <a id="5917" class="String">&quot;n&quot;</a> <a id="5921" href="plfa.part2.Lambda.html#3812" class="InductiveConstructor Operator">⇒</a> <a id="5923" href="plfa.part2.Lambda.html#3940" class="InductiveConstructor Operator">`suc</a> <a id="5928" class="Symbol">(</a><a id="5929" href="plfa.part2.Lambda.html#3773" class="InductiveConstructor Operator">`</a> <a id="5931" class="String">&quot;n&quot;</a><a id="5934" class="Symbol">)</a>
</pre>{% endraw %}The Church numeral for two takes two arguments `s` and `z`
and applies `s` twice to `z`.
Addition takes two numerals `m` and `n`, a
function `s` and an argument `z`, and it uses `m` to apply `s` to the
result of using `n` to apply `s` to `z`; hence `s` is applied `m` plus
`n` times to `z`, yielding the Church numeral for the sum of `m` and
`n`.  For convenience, we define a function that computes successor.
To convert a Church numeral to the corresponding natural, we apply
it to the `sucᶜ` function and the natural number zero.
Again, later we will confirm that two plus two is four,
in other words that the term

    plusᶜ · twoᶜ · twoᶜ · sucᶜ · `zero

reduces to `` `suc `suc `suc `suc `zero ``.


#### Exercise `mul` (recommended)

Write out the definition of a lambda term that multiplies
two natural numbers.  Your definition may use `plus` as
defined earlier.

{% raw %}<pre class="Agda"><a id="6816" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}

#### Exercise `mulᶜ` (practice)

Write out the definition of a lambda term that multiplies
two natural numbers represented as Church numerals. Your
definition may use `plusᶜ` as defined earlier (or may not
— there are nice definitions both ways).

{% raw %}<pre class="Agda"><a id="7097" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}

#### Exercise `primed` (stretch)

Some people find it annoying to write `` ` "x" `` instead of `x`.
We can make examples with lambda terms slightly easier to write
by adding the following definitions:
{% raw %}<pre class="Agda"><a id="ƛ′_⇒_"></a><a id="7331" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#7331" class="Function Operator">ƛ′_⇒_</a> <a id="7337" class="Symbol">:</a> <a id="7339" href="plfa.part2.Lambda.html#3754" class="Datatype">Term</a> <a id="7344" class="Symbol">→</a> <a id="7346" href="plfa.part2.Lambda.html#3754" class="Datatype">Term</a> <a id="7351" class="Symbol">→</a> <a id="7353" href="plfa.part2.Lambda.html#3754" class="Datatype">Term</a>
<a id="7358" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#7331" class="Function Operator">ƛ′</a> <a id="7361" class="Symbol">(</a><a id="7362" href="plfa.part2.Lambda.html#3773" class="InductiveConstructor Operator">`</a> <a id="7364" href="plfa.part2.Lambda.html#7364" class="Bound">x</a><a id="7365" class="Symbol">)</a> <a id="7367" href="plfa.part2.Lambda.html#7331" class="Function Operator">⇒</a> <a id="7369" href="plfa.part2.Lambda.html#7369" class="Bound">N</a>  <a id="7372" class="Symbol">=</a>  <a id="7375" href="plfa.part2.Lambda.html#3812" class="InductiveConstructor Operator">ƛ</a> <a id="7377" href="plfa.part2.Lambda.html#7364" class="Bound">x</a> <a id="7379" href="plfa.part2.Lambda.html#3812" class="InductiveConstructor Operator">⇒</a> <a id="7381" href="plfa.part2.Lambda.html#7369" class="Bound">N</a>
<a id="7383" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#7331" class="CatchallClause Function Operator">ƛ′</a><a id="7385" class="CatchallClause"> </a><a id="7386" class="CatchallClause Symbol">_</a><a id="7387" class="CatchallClause"> </a><a id="7388" href="plfa.part2.Lambda.html#7331" class="CatchallClause Function Operator">⇒</a><a id="7389" class="CatchallClause"> </a><a id="7390" class="CatchallClause Symbol">_</a>      <a id="7397" class="Symbol">=</a>  <a id="7400" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html#294" class="Function">⊥-elim</a> <a id="7407" href="plfa.part2.Lambda.html#7436" class="Postulate">impossible</a>
  <a id="7420" class="Keyword">where</a> <a id="7426" class="Keyword">postulate</a> <a id="7436" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#7436" class="Postulate">impossible</a> <a id="7447" class="Symbol">:</a> <a id="7449" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html#279" class="Datatype">⊥</a>

<a id="case′_[zero⇒_|suc_⇒_]"></a><a id="7452" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#7452" class="Function Operator">case′_[zero⇒_|suc_⇒_]</a> <a id="7474" class="Symbol">:</a> <a id="7476" href="plfa.part2.Lambda.html#3754" class="Datatype">Term</a> <a id="7481" class="Symbol">→</a> <a id="7483" href="plfa.part2.Lambda.html#3754" class="Datatype">Term</a> <a id="7488" class="Symbol">→</a> <a id="7490" href="plfa.part2.Lambda.html#3754" class="Datatype">Term</a> <a id="7495" class="Symbol">→</a> <a id="7497" href="plfa.part2.Lambda.html#3754" class="Datatype">Term</a> <a id="7502" class="Symbol">→</a> <a id="7504" href="plfa.part2.Lambda.html#3754" class="Datatype">Term</a>
<a id="7509" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#7452" class="Function Operator">case′</a> <a id="7515" href="plfa.part2.Lambda.html#7515" class="Bound">L</a> <a id="7517" href="plfa.part2.Lambda.html#7452" class="Function Operator">[zero⇒</a> <a id="7524" href="plfa.part2.Lambda.html#7524" class="Bound">M</a> <a id="7526" href="plfa.part2.Lambda.html#7452" class="Function Operator">|suc</a> <a id="7531" class="Symbol">(</a><a id="7532" href="plfa.part2.Lambda.html#3773" class="InductiveConstructor Operator">`</a> <a id="7534" href="plfa.part2.Lambda.html#7534" class="Bound">x</a><a id="7535" class="Symbol">)</a> <a id="7537" href="plfa.part2.Lambda.html#7452" class="Function Operator">⇒</a> <a id="7539" href="plfa.part2.Lambda.html#7539" class="Bound">N</a> <a id="7541" href="plfa.part2.Lambda.html#7452" class="Function Operator">]</a>  <a id="7544" class="Symbol">=</a>  <a id="7547" href="plfa.part2.Lambda.html#3981" class="InductiveConstructor Operator">case</a> <a id="7552" href="plfa.part2.Lambda.html#7515" class="Bound">L</a> <a id="7554" href="plfa.part2.Lambda.html#3981" class="InductiveConstructor Operator">[zero⇒</a> <a id="7561" href="plfa.part2.Lambda.html#7524" class="Bound">M</a> <a id="7563" href="plfa.part2.Lambda.html#3981" class="InductiveConstructor Operator">|suc</a> <a id="7568" href="plfa.part2.Lambda.html#7534" class="Bound">x</a> <a id="7570" href="plfa.part2.Lambda.html#3981" class="InductiveConstructor Operator">⇒</a> <a id="7572" href="plfa.part2.Lambda.html#7539" class="Bound">N</a> <a id="7574" href="plfa.part2.Lambda.html#3981" class="InductiveConstructor Operator">]</a>
<a id="7576" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#7452" class="CatchallClause Function Operator">case′</a><a id="7581" class="CatchallClause"> </a><a id="7582" class="CatchallClause Symbol">_</a><a id="7583" class="CatchallClause"> </a><a id="7584" href="plfa.part2.Lambda.html#7452" class="CatchallClause Function Operator">[zero⇒</a><a id="7590" class="CatchallClause"> </a><a id="7591" class="CatchallClause Symbol">_</a><a id="7592" class="CatchallClause"> </a><a id="7593" href="plfa.part2.Lambda.html#7452" class="CatchallClause Function Operator">|suc</a><a id="7597" class="CatchallClause"> </a><a id="7598" class="CatchallClause Symbol">_</a><a id="7599" class="CatchallClause"> </a><a id="7600" href="plfa.part2.Lambda.html#7452" class="CatchallClause Function Operator">⇒</a><a id="7601" class="CatchallClause"> </a><a id="7602" class="CatchallClause Symbol">_</a><a id="7603" class="CatchallClause"> </a><a id="7604" href="plfa.part2.Lambda.html#7452" class="CatchallClause Function Operator">]</a>      <a id="7611" class="Symbol">=</a>  <a id="7614" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html#294" class="Function">⊥-elim</a> <a id="7621" href="plfa.part2.Lambda.html#7650" class="Postulate">impossible</a>
  <a id="7634" class="Keyword">where</a> <a id="7640" class="Keyword">postulate</a> <a id="7650" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#7650" class="Postulate">impossible</a> <a id="7661" class="Symbol">:</a> <a id="7663" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html#279" class="Datatype">⊥</a>

<a id="μ′_⇒_"></a><a id="7666" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#7666" class="Function Operator">μ′_⇒_</a> <a id="7672" class="Symbol">:</a> <a id="7674" href="plfa.part2.Lambda.html#3754" class="Datatype">Term</a> <a id="7679" class="Symbol">→</a> <a id="7681" href="plfa.part2.Lambda.html#3754" class="Datatype">Term</a> <a id="7686" class="Symbol">→</a> <a id="7688" href="plfa.part2.Lambda.html#3754" class="Datatype">Term</a>
<a id="7693" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#7666" class="Function Operator">μ′</a> <a id="7696" class="Symbol">(</a><a id="7697" href="plfa.part2.Lambda.html#3773" class="InductiveConstructor Operator">`</a> <a id="7699" href="plfa.part2.Lambda.html#7699" class="Bound">x</a><a id="7700" class="Symbol">)</a> <a id="7702" href="plfa.part2.Lambda.html#7666" class="Function Operator">⇒</a> <a id="7704" href="plfa.part2.Lambda.html#7704" class="Bound">N</a>  <a id="7707" class="Symbol">=</a>  <a id="7710" href="plfa.part2.Lambda.html#4041" class="InductiveConstructor Operator">μ</a> <a id="7712" href="plfa.part2.Lambda.html#7699" class="Bound">x</a> <a id="7714" href="plfa.part2.Lambda.html#4041" class="InductiveConstructor Operator">⇒</a> <a id="7716" href="plfa.part2.Lambda.html#7704" class="Bound">N</a>
<a id="7718" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#7666" class="CatchallClause Function Operator">μ′</a><a id="7720" class="CatchallClause"> </a><a id="7721" class="CatchallClause Symbol">_</a><a id="7722" class="CatchallClause"> </a><a id="7723" href="plfa.part2.Lambda.html#7666" class="CatchallClause Function Operator">⇒</a><a id="7724" class="CatchallClause"> </a><a id="7725" class="CatchallClause Symbol">_</a>      <a id="7732" class="Symbol">=</a>  <a id="7735" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html#294" class="Function">⊥-elim</a> <a id="7742" href="plfa.part2.Lambda.html#7771" class="Postulate">impossible</a>
  <a id="7755" class="Keyword">where</a> <a id="7761" class="Keyword">postulate</a> <a id="7771" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#7771" class="Postulate">impossible</a> <a id="7782" class="Symbol">:</a> <a id="7784" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html#279" class="Datatype">⊥</a>
</pre>{% endraw %}The definition of `plus` can now be written as follows:
{% raw %}<pre class="Agda"><a id="plus′"></a><a id="7850" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#7850" class="Function">plus′</a> <a id="7856" class="Symbol">:</a> <a id="7858" href="plfa.part2.Lambda.html#3754" class="Datatype">Term</a>
<a id="7863" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#7850" class="Function">plus′</a> <a id="7869" class="Symbol">=</a> <a id="7871" href="plfa.part2.Lambda.html#7666" class="Function Operator">μ′</a> <a id="7874" href="plfa.part2.Lambda.html#7981" class="Function">+</a> <a id="7876" href="plfa.part2.Lambda.html#7666" class="Function Operator">⇒</a> <a id="7878" href="plfa.part2.Lambda.html#7331" class="Function Operator">ƛ′</a> <a id="7881" href="plfa.part2.Lambda.html#7995" class="Function">m</a> <a id="7883" href="plfa.part2.Lambda.html#7331" class="Function Operator">⇒</a> <a id="7885" href="plfa.part2.Lambda.html#7331" class="Function Operator">ƛ′</a> <a id="7888" href="plfa.part2.Lambda.html#8009" class="Function">n</a> <a id="7890" href="plfa.part2.Lambda.html#7331" class="Function Operator">⇒</a>
          <a id="7902" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#7452" class="Function Operator">case′</a> <a id="7908" href="plfa.part2.Lambda.html#7995" class="Function">m</a>
            <a id="7922" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#7452" class="Function Operator">[zero⇒</a> <a id="7929" href="plfa.part2.Lambda.html#8009" class="Function">n</a>
            <a id="7943" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#7452" class="Function Operator">|suc</a> <a id="7948" href="plfa.part2.Lambda.html#7995" class="Function">m</a> <a id="7950" href="plfa.part2.Lambda.html#7452" class="Function Operator">⇒</a> <a id="7952" href="plfa.part2.Lambda.html#3940" class="InductiveConstructor Operator">`suc</a> <a id="7957" class="Symbol">(</a><a id="7958" href="plfa.part2.Lambda.html#7981" class="Function">+</a> <a id="7960" href="plfa.part2.Lambda.html#3858" class="InductiveConstructor Operator">·</a> <a id="7962" href="plfa.part2.Lambda.html#7995" class="Function">m</a> <a id="7964" href="plfa.part2.Lambda.html#3858" class="InductiveConstructor Operator">·</a> <a id="7966" href="plfa.part2.Lambda.html#8009" class="Function">n</a><a id="7967" class="Symbol">)</a> <a id="7969" href="plfa.part2.Lambda.html#7452" class="Function Operator">]</a>
  <a id="7973" class="Keyword">where</a>
  <a id="7981" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#7981" class="Function">+</a>  <a id="7984" class="Symbol">=</a>  <a id="7987" href="plfa.part2.Lambda.html#3773" class="InductiveConstructor Operator">`</a> <a id="7989" class="String">&quot;+&quot;</a>
  <a id="7995" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#7995" class="Function">m</a>  <a id="7998" class="Symbol">=</a>  <a id="8001" href="plfa.part2.Lambda.html#3773" class="InductiveConstructor Operator">`</a> <a id="8003" class="String">&quot;m&quot;</a>
  <a id="8009" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#8009" class="Function">n</a>  <a id="8012" class="Symbol">=</a>  <a id="8015" href="plfa.part2.Lambda.html#3773" class="InductiveConstructor Operator">`</a> <a id="8017" class="String">&quot;n&quot;</a>
</pre>{% endraw %}Write out the definition of multiplication in the same style.


### Formal vs informal

In informal presentation of formal semantics, one uses choice of
variable name to disambiguate and writes `x` rather than `` ` x ``
for a term that is a variable. Agda requires we distinguish.

Similarly, informal presentation often use the same notation for
function types, lambda abstraction, and function application in both
the _object language_ (the language one is describing) and the
_meta-language_ (the language in which the description is written),
trusting readers can use context to distinguish the two.  Agda is
not quite so forgiving, so here we use `ƛ x ⇒ N` and `L · M` for the
object language, as compared to `λ x → N` and `L M` in our
meta-language, Agda.


### Bound and free variables

In an abstraction `ƛ x ⇒ N` we call `x` the _bound_ variable
and `N` the _body_ of the abstraction.  A central feature
of lambda calculus is that consistent renaming of bound variables
leaves the meaning of a term unchanged.  Thus the five terms

* `` ƛ "s" ⇒ ƛ "z" ⇒ ` "s" · (` "s" · ` "z") ``
* `` ƛ "f" ⇒ ƛ "x" ⇒ ` "f" · (` "f" · ` "x") ``
* `` ƛ "sam" ⇒ ƛ "zelda" ⇒ ` "sam" · (` "sam" · ` "zelda") ``
* `` ƛ "z" ⇒ ƛ "s" ⇒ ` "z" · (` "z" · ` "s") ``
* `` ƛ "😇" ⇒ ƛ "😈" ⇒ ` "😇" · (` "😇" · ` "😈" ) ``

are all considered equivalent.  Following the convention introduced
by Haskell Curry, who used the Greek letter `α` (_alpha_) to label such rules,
this equivalence relation is called _alpha renaming_.

As we descend from a term into its subterms, variables
that are bound may become free.  Consider the following terms:

* `` ƛ "s" ⇒ ƛ "z" ⇒ ` "s" · (` "s" · ` "z") ``
  has both `s` and `z` as bound variables.

* `` ƛ "z" ⇒ ` "s" · (` "s" · ` "z") ``
  has `z` bound and `s` free.

* `` ` "s" · (` "s" · ` "z") ``
  has both `s` and `z` as free variables.

We say that a term with no free variables is _closed_; otherwise it is
_open_.  Of the three terms above, the first is closed and the other
two are open.  We will focus on reduction of closed terms.

Different occurrences of a variable may be bound and free.
In the term

    (ƛ "x" ⇒ ` "x") · ` "x"

the inner occurrence of `x` is bound while the outer occurrence is free.
By alpha renaming, the term above is equivalent to

    (ƛ "y" ⇒ ` "y") · ` "x"

in which `y` is bound and `x` is free.  A common convention, called the
_Barendregt convention_, is to use alpha renaming to ensure that the bound
variables in a term are distinct from the free variables, which can
avoid confusions that may arise if bound and free variables have the
same names.

Case and recursion also introduce bound variables, which are also subject
to alpha renaming. In the term

    μ "+" ⇒ ƛ "m" ⇒ ƛ "n" ⇒
      case ` "m"
        [zero⇒ ` "n"
        |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n") ]

notice that there are two binding occurrences of `m`, one in the first
line and one in the last line.  It is equivalent to the following term,

    μ "plus" ⇒ ƛ "x" ⇒ ƛ "y" ⇒
      case ` "x"
        [zero⇒ ` "y"
        |suc "x′" ⇒ `suc (` "plus" · ` "x′" · ` "y") ]

where the two binding occurrences corresponding to `m` now have distinct
names, `x` and `x′`.


## Values

A _value_ is a term that corresponds to an answer.
Thus, `` `suc `suc `suc `suc `zero `` is a value,
while `` plus · two · two `` is not.
Following convention, we treat all function abstractions
as values; thus, `` plus `` by itself is considered a value.

The predicate `Value M` holds if term `M` is a value:

{% raw %}<pre class="Agda"><a id="11548" class="Keyword">data</a> <a id="Value"></a><a id="11553" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#11553" class="Datatype">Value</a> <a id="11559" class="Symbol">:</a> <a id="11561" href="plfa.part2.Lambda.html#3754" class="Datatype">Term</a> <a id="11566" class="Symbol">→</a> <a id="11568" class="PrimitiveType">Set</a> <a id="11572" class="Keyword">where</a>

  <a id="Value.V-ƛ"></a><a id="11581" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#11581" class="InductiveConstructor">V-ƛ</a> <a id="11585" class="Symbol">:</a> <a id="11587" class="Symbol">∀</a> <a id="11589" class="Symbol">{</a><a id="11590" href="plfa.part2.Lambda.html#11590" class="Bound">x</a> <a id="11592" href="plfa.part2.Lambda.html#11592" class="Bound">N</a><a id="11593" class="Symbol">}</a>
      <a id="11601" class="Comment">---------------</a>
    <a id="11621" class="Symbol">→</a> <a id="11623" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#11553" class="Datatype">Value</a> <a id="11629" class="Symbol">(</a><a id="11630" href="plfa.part2.Lambda.html#3812" class="InductiveConstructor Operator">ƛ</a> <a id="11632" href="plfa.part2.Lambda.html#11590" class="Bound">x</a> <a id="11634" href="plfa.part2.Lambda.html#3812" class="InductiveConstructor Operator">⇒</a> <a id="11636" href="plfa.part2.Lambda.html#11592" class="Bound">N</a><a id="11637" class="Symbol">)</a>

  <a id="Value.V-zero"></a><a id="11642" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#11642" class="InductiveConstructor">V-zero</a> <a id="11649" class="Symbol">:</a>
      <a id="11657" class="Comment">-----------</a>
      <a id="11675" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#11553" class="Datatype">Value</a> <a id="11681" href="plfa.part2.Lambda.html#3906" class="InductiveConstructor">`zero</a>

  <a id="Value.V-suc"></a><a id="11690" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#11690" class="InductiveConstructor">V-suc</a> <a id="11696" class="Symbol">:</a> <a id="11698" class="Symbol">∀</a> <a id="11700" class="Symbol">{</a><a id="11701" href="plfa.part2.Lambda.html#11701" class="Bound">V</a><a id="11702" class="Symbol">}</a>
    <a id="11708" class="Symbol">→</a> <a id="11710" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#11553" class="Datatype">Value</a> <a id="11716" href="plfa.part2.Lambda.html#11701" class="Bound">V</a>
      <a id="11724" class="Comment">--------------</a>
    <a id="11743" class="Symbol">→</a> <a id="11745" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#11553" class="Datatype">Value</a> <a id="11751" class="Symbol">(</a><a id="11752" href="plfa.part2.Lambda.html#3940" class="InductiveConstructor Operator">`suc</a> <a id="11757" href="plfa.part2.Lambda.html#11701" class="Bound">V</a><a id="11758" class="Symbol">)</a>
</pre>{% endraw %}
In what follows, we let `V` and `W` range over values.


### Formal vs informal

In informal presentations of formal semantics, using
`V` as the name of a metavariable is sufficient to
indicate that it is a value. In Agda, we must explicitly
invoke the `Value` predicate.

### Other approaches

An alternative is not to focus on closed terms,
to treat variables as values, and to treat
`ƛ x ⇒ N` as a value only if `N` is a value.
Indeed, this is how Agda normalises terms.
We consider this approach in
Chapter [Untyped]({{ site.baseurl }}/Untyped/).


## Substitution

The heart of lambda calculus is the operation of
substituting one term for a variable in another term.
Substitution plays a key role in defining the
operational semantics of function application.
For instance, we have

      (ƛ "s" ⇒ ƛ "z" ⇒ ` "s" · (` "s" · ` "z")) · sucᶜ · `zero
    —→
      (ƛ "z" ⇒ sucᶜ · (sucᶜ · "z")) · `zero
    —→
      sucᶜ · (sucᶜ · `zero)

where we substitute `sucᶜ` for `` ` "s" `` and `` `zero `` for `` ` "z" ``
in the body of the function abstraction.

We write substitution as `N [ x := V ]`, meaning
"substitute term `V` for free occurrences of variable `x` in term `N`",
or, more compactly, "substitute `V` for `x` in `N`",
or equivalently, "in `N` replace `x` by `V`".
Substitution works if `V` is any closed term;
it need not be a value, but we use `V` since in fact we
usually substitute values.

Here are some examples:

* `` (ƛ "z" ⇒ ` "s" · (` "s" · ` "z")) [ "s" := sucᶜ ] `` yields
  `` ƛ "z" ⇒ sucᶜ · (sucᶜ · ` "z") ``.
* `` (sucᶜ · (sucᶜ · ` "z")) [ "z" := `zero ] `` yields
  `` sucᶜ · (sucᶜ · `zero) ``.
* `` (ƛ "x" ⇒ ` "y") [ "y" := `zero ] `` yields `` ƛ "x" ⇒ `zero ``.
* `` (ƛ "x" ⇒ ` "x") [ "x" := `zero ] `` yields `` ƛ "x" ⇒ ` "x" ``.
* `` (ƛ "y" ⇒ ` "y") [ "x" := `zero ] `` yields `` ƛ "y" ⇒ ` "y" ``.

In the last but one example, substituting `` `zero `` for `x` in
`` ƛ "x" ⇒ ` "x" `` does _not_ yield `` ƛ "x" ⇒ `zero ``,
since `x` is bound in the lambda abstraction.
The choice of bound names is irrelevant: both
`` ƛ "x" ⇒ ` "x" `` and `` ƛ "y" ⇒ ` "y" `` stand for the
identity function.  One way to think of this is that `x` within
the body of the abstraction stands for a _different_ variable than
`x` outside the abstraction, they just happen to have the same name.

We will give a definition of substitution that is only valid
when term substituted for the variable is closed. This is because
substitution by terms that are _not_ closed may require renaming
of bound variables. For example:

* `` (ƛ "x" ⇒ ` "x" · ` "y") [ "y" := ` "x" · `zero] `` should not yield <br/>
  `` (ƛ "x" ⇒ ` "x" · (` "x" · `zero)) ``.

Instead, we should rename the bound variable to avoid capture:

* `` (ƛ "x" ⇒ ` "x" · ` "y") [ "y" := ` "x" · `zero ] `` should yield <br/>
  `` ƛ "x′" ⇒ ` "x′" · (` "x" · `zero) ``.

Here `x′` is a fresh variable distinct from `x`.
Formal definition of substitution with suitable renaming is considerably
more complex, so we avoid it by restricting to substitution by closed terms,
which will be adequate for our purposes.

Here is the formal definition of substitution by closed terms in Agda:

{% raw %}<pre class="Agda"><a id="14919" class="Keyword">infix</a> <a id="14925" class="Number">9</a> <a id="14927" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#14936" class="Function Operator">_[_:=_]</a>

<a id="_[_:=_]"></a><a id="14936" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#14936" class="Function Operator">_[_:=_]</a> <a id="14944" class="Symbol">:</a> <a id="14946" href="plfa.part2.Lambda.html#3754" class="Datatype">Term</a> <a id="14951" class="Symbol">→</a> <a id="14953" href="plfa.part2.Lambda.html#3653" class="Function">Id</a> <a id="14956" class="Symbol">→</a> <a id="14958" href="plfa.part2.Lambda.html#3754" class="Datatype">Term</a> <a id="14963" class="Symbol">→</a> <a id="14965" href="plfa.part2.Lambda.html#3754" class="Datatype">Term</a>
<a id="14970" class="Symbol">(</a><a id="14971" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3773" class="InductiveConstructor Operator">`</a> <a id="14973" href="plfa.part2.Lambda.html#14973" class="Bound">x</a><a id="14974" class="Symbol">)</a> <a id="14976" href="plfa.part2.Lambda.html#14936" class="Function Operator">[</a> <a id="14978" href="plfa.part2.Lambda.html#14978" class="Bound">y</a> <a id="14980" href="plfa.part2.Lambda.html#14936" class="Function Operator">:=</a> <a id="14983" href="plfa.part2.Lambda.html#14983" class="Bound">V</a> <a id="14985" href="plfa.part2.Lambda.html#14936" class="Function Operator">]</a> <a id="14987" class="Keyword">with</a> <a id="14992" href="plfa.part2.Lambda.html#14973" class="Bound">x</a> <a id="14994" href="https://agda.github.io/agda-stdlib/v1.1/Data.String.Properties.html#2569" class="Function Operator">≟</a> <a id="14996" href="plfa.part2.Lambda.html#14978" class="Bound">y</a>
<a id="14998" class="Symbol">...</a> <a id="15002" class="Symbol">|</a> <a id="15004" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#641" class="InductiveConstructor">yes</a> <a id="15008" class="Symbol">_</a>          <a id="15019" class="Symbol">=</a>  <a id="15022" class="Bound">V</a>
<a id="15024" class="Symbol">...</a> <a id="15028" class="Symbol">|</a> <a id="15030" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#668" class="InductiveConstructor">no</a>  <a id="15034" class="Symbol">_</a>          <a id="15045" class="Symbol">=</a>  <a id="15048" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3773" class="InductiveConstructor Operator">`</a> <a id="15050" class="Bound">x</a>
<a id="15052" class="Symbol">(</a><a id="15053" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3812" class="InductiveConstructor Operator">ƛ</a> <a id="15055" href="plfa.part2.Lambda.html#15055" class="Bound">x</a> <a id="15057" href="plfa.part2.Lambda.html#3812" class="InductiveConstructor Operator">⇒</a> <a id="15059" href="plfa.part2.Lambda.html#15059" class="Bound">N</a><a id="15060" class="Symbol">)</a> <a id="15062" href="plfa.part2.Lambda.html#14936" class="Function Operator">[</a> <a id="15064" href="plfa.part2.Lambda.html#15064" class="Bound">y</a> <a id="15066" href="plfa.part2.Lambda.html#14936" class="Function Operator">:=</a> <a id="15069" href="plfa.part2.Lambda.html#15069" class="Bound">V</a> <a id="15071" href="plfa.part2.Lambda.html#14936" class="Function Operator">]</a> <a id="15073" class="Keyword">with</a> <a id="15078" href="plfa.part2.Lambda.html#15055" class="Bound">x</a> <a id="15080" href="https://agda.github.io/agda-stdlib/v1.1/Data.String.Properties.html#2569" class="Function Operator">≟</a> <a id="15082" href="plfa.part2.Lambda.html#15064" class="Bound">y</a>
<a id="15084" class="Symbol">...</a> <a id="15088" class="Symbol">|</a> <a id="15090" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#641" class="InductiveConstructor">yes</a> <a id="15094" class="Symbol">_</a>          <a id="15105" class="Symbol">=</a>  <a id="15108" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3812" class="InductiveConstructor Operator">ƛ</a> <a id="15110" class="Bound">x</a> <a id="15112" href="plfa.part2.Lambda.html#3812" class="InductiveConstructor Operator">⇒</a> <a id="15114" class="Bound">N</a>
<a id="15116" class="Symbol">...</a> <a id="15120" class="Symbol">|</a> <a id="15122" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#668" class="InductiveConstructor">no</a>  <a id="15126" class="Symbol">_</a>          <a id="15137" class="Symbol">=</a>  <a id="15140" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3812" class="InductiveConstructor Operator">ƛ</a> <a id="15142" class="Bound">x</a> <a id="15144" href="plfa.part2.Lambda.html#3812" class="InductiveConstructor Operator">⇒</a> <a id="15146" class="Bound">N</a> <a id="15148" href="plfa.part2.Lambda.html#14936" class="Function Operator">[</a> <a id="15150" class="Bound">y</a> <a id="15152" href="plfa.part2.Lambda.html#14936" class="Function Operator">:=</a> <a id="15155" class="Bound">V</a> <a id="15157" href="plfa.part2.Lambda.html#14936" class="Function Operator">]</a>
<a id="15159" class="Symbol">(</a><a id="15160" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#15160" class="Bound">L</a> <a id="15162" href="plfa.part2.Lambda.html#3858" class="InductiveConstructor Operator">·</a> <a id="15164" href="plfa.part2.Lambda.html#15164" class="Bound">M</a><a id="15165" class="Symbol">)</a> <a id="15167" href="plfa.part2.Lambda.html#14936" class="Function Operator">[</a> <a id="15169" href="plfa.part2.Lambda.html#15169" class="Bound">y</a> <a id="15171" href="plfa.part2.Lambda.html#14936" class="Function Operator">:=</a> <a id="15174" href="plfa.part2.Lambda.html#15174" class="Bound">V</a> <a id="15176" href="plfa.part2.Lambda.html#14936" class="Function Operator">]</a>   <a id="15180" class="Symbol">=</a>  <a id="15183" href="plfa.part2.Lambda.html#15160" class="Bound">L</a> <a id="15185" href="plfa.part2.Lambda.html#14936" class="Function Operator">[</a> <a id="15187" href="plfa.part2.Lambda.html#15169" class="Bound">y</a> <a id="15189" href="plfa.part2.Lambda.html#14936" class="Function Operator">:=</a> <a id="15192" href="plfa.part2.Lambda.html#15174" class="Bound">V</a> <a id="15194" href="plfa.part2.Lambda.html#14936" class="Function Operator">]</a> <a id="15196" href="plfa.part2.Lambda.html#3858" class="InductiveConstructor Operator">·</a> <a id="15198" href="plfa.part2.Lambda.html#15164" class="Bound">M</a> <a id="15200" href="plfa.part2.Lambda.html#14936" class="Function Operator">[</a> <a id="15202" href="plfa.part2.Lambda.html#15169" class="Bound">y</a> <a id="15204" href="plfa.part2.Lambda.html#14936" class="Function Operator">:=</a> <a id="15207" href="plfa.part2.Lambda.html#15174" class="Bound">V</a> <a id="15209" href="plfa.part2.Lambda.html#14936" class="Function Operator">]</a>
<a id="15211" class="Symbol">(</a><a id="15212" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3906" class="InductiveConstructor">`zero</a><a id="15217" class="Symbol">)</a> <a id="15219" href="plfa.part2.Lambda.html#14936" class="Function Operator">[</a> <a id="15221" href="plfa.part2.Lambda.html#15221" class="Bound">y</a> <a id="15223" href="plfa.part2.Lambda.html#14936" class="Function Operator">:=</a> <a id="15226" href="plfa.part2.Lambda.html#15226" class="Bound">V</a> <a id="15228" href="plfa.part2.Lambda.html#14936" class="Function Operator">]</a>   <a id="15232" class="Symbol">=</a>  <a id="15235" href="plfa.part2.Lambda.html#3906" class="InductiveConstructor">`zero</a>
<a id="15241" class="Symbol">(</a><a id="15242" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3940" class="InductiveConstructor Operator">`suc</a> <a id="15247" href="plfa.part2.Lambda.html#15247" class="Bound">M</a><a id="15248" class="Symbol">)</a> <a id="15250" href="plfa.part2.Lambda.html#14936" class="Function Operator">[</a> <a id="15252" href="plfa.part2.Lambda.html#15252" class="Bound">y</a> <a id="15254" href="plfa.part2.Lambda.html#14936" class="Function Operator">:=</a> <a id="15257" href="plfa.part2.Lambda.html#15257" class="Bound">V</a> <a id="15259" href="plfa.part2.Lambda.html#14936" class="Function Operator">]</a>  <a id="15262" class="Symbol">=</a>  <a id="15265" href="plfa.part2.Lambda.html#3940" class="InductiveConstructor Operator">`suc</a> <a id="15270" href="plfa.part2.Lambda.html#15247" class="Bound">M</a> <a id="15272" href="plfa.part2.Lambda.html#14936" class="Function Operator">[</a> <a id="15274" href="plfa.part2.Lambda.html#15252" class="Bound">y</a> <a id="15276" href="plfa.part2.Lambda.html#14936" class="Function Operator">:=</a> <a id="15279" href="plfa.part2.Lambda.html#15257" class="Bound">V</a> <a id="15281" href="plfa.part2.Lambda.html#14936" class="Function Operator">]</a>
<a id="15283" class="Symbol">(</a><a id="15284" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3981" class="InductiveConstructor Operator">case</a> <a id="15289" href="plfa.part2.Lambda.html#15289" class="Bound">L</a> <a id="15291" href="plfa.part2.Lambda.html#3981" class="InductiveConstructor Operator">[zero⇒</a> <a id="15298" href="plfa.part2.Lambda.html#15298" class="Bound">M</a> <a id="15300" href="plfa.part2.Lambda.html#3981" class="InductiveConstructor Operator">|suc</a> <a id="15305" href="plfa.part2.Lambda.html#15305" class="Bound">x</a> <a id="15307" href="plfa.part2.Lambda.html#3981" class="InductiveConstructor Operator">⇒</a> <a id="15309" href="plfa.part2.Lambda.html#15309" class="Bound">N</a> <a id="15311" href="plfa.part2.Lambda.html#3981" class="InductiveConstructor Operator">]</a><a id="15312" class="Symbol">)</a> <a id="15314" href="plfa.part2.Lambda.html#14936" class="Function Operator">[</a> <a id="15316" href="plfa.part2.Lambda.html#15316" class="Bound">y</a> <a id="15318" href="plfa.part2.Lambda.html#14936" class="Function Operator">:=</a> <a id="15321" href="plfa.part2.Lambda.html#15321" class="Bound">V</a> <a id="15323" href="plfa.part2.Lambda.html#14936" class="Function Operator">]</a> <a id="15325" class="Keyword">with</a> <a id="15330" href="plfa.part2.Lambda.html#15305" class="Bound">x</a> <a id="15332" href="https://agda.github.io/agda-stdlib/v1.1/Data.String.Properties.html#2569" class="Function Operator">≟</a> <a id="15334" href="plfa.part2.Lambda.html#15316" class="Bound">y</a>
<a id="15336" class="Symbol">...</a> <a id="15340" class="Symbol">|</a> <a id="15342" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#641" class="InductiveConstructor">yes</a> <a id="15346" class="Symbol">_</a>          <a id="15357" class="Symbol">=</a>  <a id="15360" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3981" class="InductiveConstructor Operator">case</a> <a id="15365" class="Bound">L</a> <a id="15367" href="plfa.part2.Lambda.html#14936" class="Function Operator">[</a> <a id="15369" class="Bound">y</a> <a id="15371" href="plfa.part2.Lambda.html#14936" class="Function Operator">:=</a> <a id="15374" class="Bound">V</a> <a id="15376" href="plfa.part2.Lambda.html#14936" class="Function Operator">]</a> <a id="15378" href="plfa.part2.Lambda.html#3981" class="InductiveConstructor Operator">[zero⇒</a> <a id="15385" class="Bound">M</a> <a id="15387" href="plfa.part2.Lambda.html#14936" class="Function Operator">[</a> <a id="15389" class="Bound">y</a> <a id="15391" href="plfa.part2.Lambda.html#14936" class="Function Operator">:=</a> <a id="15394" class="Bound">V</a> <a id="15396" href="plfa.part2.Lambda.html#14936" class="Function Operator">]</a> <a id="15398" href="plfa.part2.Lambda.html#3981" class="InductiveConstructor Operator">|suc</a> <a id="15403" class="Bound">x</a> <a id="15405" href="plfa.part2.Lambda.html#3981" class="InductiveConstructor Operator">⇒</a> <a id="15407" class="Bound">N</a> <a id="15409" href="plfa.part2.Lambda.html#3981" class="InductiveConstructor Operator">]</a>
<a id="15411" class="Symbol">...</a> <a id="15415" class="Symbol">|</a> <a id="15417" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#668" class="InductiveConstructor">no</a>  <a id="15421" class="Symbol">_</a>          <a id="15432" class="Symbol">=</a>  <a id="15435" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3981" class="InductiveConstructor Operator">case</a> <a id="15440" class="Bound">L</a> <a id="15442" href="plfa.part2.Lambda.html#14936" class="Function Operator">[</a> <a id="15444" class="Bound">y</a> <a id="15446" href="plfa.part2.Lambda.html#14936" class="Function Operator">:=</a> <a id="15449" class="Bound">V</a> <a id="15451" href="plfa.part2.Lambda.html#14936" class="Function Operator">]</a> <a id="15453" href="plfa.part2.Lambda.html#3981" class="InductiveConstructor Operator">[zero⇒</a> <a id="15460" class="Bound">M</a> <a id="15462" href="plfa.part2.Lambda.html#14936" class="Function Operator">[</a> <a id="15464" class="Bound">y</a> <a id="15466" href="plfa.part2.Lambda.html#14936" class="Function Operator">:=</a> <a id="15469" class="Bound">V</a> <a id="15471" href="plfa.part2.Lambda.html#14936" class="Function Operator">]</a> <a id="15473" href="plfa.part2.Lambda.html#3981" class="InductiveConstructor Operator">|suc</a> <a id="15478" class="Bound">x</a> <a id="15480" href="plfa.part2.Lambda.html#3981" class="InductiveConstructor Operator">⇒</a> <a id="15482" class="Bound">N</a> <a id="15484" href="plfa.part2.Lambda.html#14936" class="Function Operator">[</a> <a id="15486" class="Bound">y</a> <a id="15488" href="plfa.part2.Lambda.html#14936" class="Function Operator">:=</a> <a id="15491" class="Bound">V</a> <a id="15493" href="plfa.part2.Lambda.html#14936" class="Function Operator">]</a> <a id="15495" href="plfa.part2.Lambda.html#3981" class="InductiveConstructor Operator">]</a>
<a id="15497" class="Symbol">(</a><a id="15498" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#4041" class="InductiveConstructor Operator">μ</a> <a id="15500" href="plfa.part2.Lambda.html#15500" class="Bound">x</a> <a id="15502" href="plfa.part2.Lambda.html#4041" class="InductiveConstructor Operator">⇒</a> <a id="15504" href="plfa.part2.Lambda.html#15504" class="Bound">N</a><a id="15505" class="Symbol">)</a> <a id="15507" href="plfa.part2.Lambda.html#14936" class="Function Operator">[</a> <a id="15509" href="plfa.part2.Lambda.html#15509" class="Bound">y</a> <a id="15511" href="plfa.part2.Lambda.html#14936" class="Function Operator">:=</a> <a id="15514" href="plfa.part2.Lambda.html#15514" class="Bound">V</a> <a id="15516" href="plfa.part2.Lambda.html#14936" class="Function Operator">]</a> <a id="15518" class="Keyword">with</a> <a id="15523" href="plfa.part2.Lambda.html#15500" class="Bound">x</a> <a id="15525" href="https://agda.github.io/agda-stdlib/v1.1/Data.String.Properties.html#2569" class="Function Operator">≟</a> <a id="15527" href="plfa.part2.Lambda.html#15509" class="Bound">y</a>
<a id="15529" class="Symbol">...</a> <a id="15533" class="Symbol">|</a> <a id="15535" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#641" class="InductiveConstructor">yes</a> <a id="15539" class="Symbol">_</a>          <a id="15550" class="Symbol">=</a>  <a id="15553" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#4041" class="InductiveConstructor Operator">μ</a> <a id="15555" class="Bound">x</a> <a id="15557" href="plfa.part2.Lambda.html#4041" class="InductiveConstructor Operator">⇒</a> <a id="15559" class="Bound">N</a>
<a id="15561" class="Symbol">...</a> <a id="15565" class="Symbol">|</a> <a id="15567" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#668" class="InductiveConstructor">no</a>  <a id="15571" class="Symbol">_</a>          <a id="15582" class="Symbol">=</a>  <a id="15585" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#4041" class="InductiveConstructor Operator">μ</a> <a id="15587" class="Bound">x</a> <a id="15589" href="plfa.part2.Lambda.html#4041" class="InductiveConstructor Operator">⇒</a> <a id="15591" class="Bound">N</a> <a id="15593" href="plfa.part2.Lambda.html#14936" class="Function Operator">[</a> <a id="15595" class="Bound">y</a> <a id="15597" href="plfa.part2.Lambda.html#14936" class="Function Operator">:=</a> <a id="15600" class="Bound">V</a> <a id="15602" href="plfa.part2.Lambda.html#14936" class="Function Operator">]</a>
</pre>{% endraw %}
Let's unpack the first three cases:

* For variables, we compare `y`, the substituted variable,
with `x`, the variable in the term. If they are the same,
we yield `V`, otherwise we yield `x` unchanged.

* For abstractions, we compare `y`, the substituted variable,
with `x`, the variable bound in the abstraction. If they are the same,
we yield the abstraction unchanged, otherwise we substitute inside the body.

* For application, we recursively substitute in the function
and the argument.

Case expressions and recursion also have bound variables that are
treated similarly to those in lambda abstractions.  Otherwise we
simply push substitution recursively into the subterms.


### Examples

Here is confirmation that the examples above are correct:

{% raw %}<pre class="Agda"><a id="16369" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#16369" class="Function">_</a> <a id="16371" class="Symbol">:</a> <a id="16373" class="Symbol">(</a><a id="16374" href="plfa.part2.Lambda.html#3812" class="InductiveConstructor Operator">ƛ</a> <a id="16376" class="String">&quot;z&quot;</a> <a id="16380" href="plfa.part2.Lambda.html#3812" class="InductiveConstructor Operator">⇒</a> <a id="16382" href="plfa.part2.Lambda.html#3773" class="InductiveConstructor Operator">`</a> <a id="16384" class="String">&quot;s&quot;</a> <a id="16388" href="plfa.part2.Lambda.html#3858" class="InductiveConstructor Operator">·</a> <a id="16390" class="Symbol">(</a><a id="16391" href="plfa.part2.Lambda.html#3773" class="InductiveConstructor Operator">`</a> <a id="16393" class="String">&quot;s&quot;</a> <a id="16397" href="plfa.part2.Lambda.html#3858" class="InductiveConstructor Operator">·</a> <a id="16399" href="plfa.part2.Lambda.html#3773" class="InductiveConstructor Operator">`</a> <a id="16401" class="String">&quot;z&quot;</a><a id="16404" class="Symbol">))</a> <a id="16407" href="plfa.part2.Lambda.html#14936" class="Function Operator">[</a> <a id="16409" class="String">&quot;s&quot;</a> <a id="16413" href="plfa.part2.Lambda.html#14936" class="Function Operator">:=</a> <a id="16416" href="plfa.part2.Lambda.html#5896" class="Function">sucᶜ</a> <a id="16421" href="plfa.part2.Lambda.html#14936" class="Function Operator">]</a> <a id="16423" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="16425" href="plfa.part2.Lambda.html#3812" class="InductiveConstructor Operator">ƛ</a> <a id="16427" class="String">&quot;z&quot;</a> <a id="16431" href="plfa.part2.Lambda.html#3812" class="InductiveConstructor Operator">⇒</a> <a id="16433" href="plfa.part2.Lambda.html#5896" class="Function">sucᶜ</a> <a id="16438" href="plfa.part2.Lambda.html#3858" class="InductiveConstructor Operator">·</a> <a id="16440" class="Symbol">(</a><a id="16441" href="plfa.part2.Lambda.html#5896" class="Function">sucᶜ</a> <a id="16446" href="plfa.part2.Lambda.html#3858" class="InductiveConstructor Operator">·</a> <a id="16448" href="plfa.part2.Lambda.html#3773" class="InductiveConstructor Operator">`</a> <a id="16450" class="String">&quot;z&quot;</a><a id="16453" class="Symbol">)</a>
<a id="16455" class="Symbol">_</a> <a id="16457" class="Symbol">=</a> <a id="16459" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>

<a id="16465" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#16465" class="Function">_</a> <a id="16467" class="Symbol">:</a> <a id="16469" class="Symbol">(</a><a id="16470" href="plfa.part2.Lambda.html#5896" class="Function">sucᶜ</a> <a id="16475" href="plfa.part2.Lambda.html#3858" class="InductiveConstructor Operator">·</a> <a id="16477" class="Symbol">(</a><a id="16478" href="plfa.part2.Lambda.html#5896" class="Function">sucᶜ</a> <a id="16483" href="plfa.part2.Lambda.html#3858" class="InductiveConstructor Operator">·</a> <a id="16485" href="plfa.part2.Lambda.html#3773" class="InductiveConstructor Operator">`</a> <a id="16487" class="String">&quot;z&quot;</a><a id="16490" class="Symbol">))</a> <a id="16493" href="plfa.part2.Lambda.html#14936" class="Function Operator">[</a> <a id="16495" class="String">&quot;z&quot;</a> <a id="16499" href="plfa.part2.Lambda.html#14936" class="Function Operator">:=</a> <a id="16502" href="plfa.part2.Lambda.html#3906" class="InductiveConstructor">`zero</a> <a id="16508" href="plfa.part2.Lambda.html#14936" class="Function Operator">]</a> <a id="16510" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="16512" href="plfa.part2.Lambda.html#5896" class="Function">sucᶜ</a> <a id="16517" href="plfa.part2.Lambda.html#3858" class="InductiveConstructor Operator">·</a> <a id="16519" class="Symbol">(</a><a id="16520" href="plfa.part2.Lambda.html#5896" class="Function">sucᶜ</a> <a id="16525" href="plfa.part2.Lambda.html#3858" class="InductiveConstructor Operator">·</a> <a id="16527" href="plfa.part2.Lambda.html#3906" class="InductiveConstructor">`zero</a><a id="16532" class="Symbol">)</a>
<a id="16534" class="Symbol">_</a> <a id="16536" class="Symbol">=</a> <a id="16538" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>

<a id="16544" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#16544" class="Function">_</a> <a id="16546" class="Symbol">:</a> <a id="16548" class="Symbol">(</a><a id="16549" href="plfa.part2.Lambda.html#3812" class="InductiveConstructor Operator">ƛ</a> <a id="16551" class="String">&quot;x&quot;</a> <a id="16555" href="plfa.part2.Lambda.html#3812" class="InductiveConstructor Operator">⇒</a> <a id="16557" href="plfa.part2.Lambda.html#3773" class="InductiveConstructor Operator">`</a> <a id="16559" class="String">&quot;y&quot;</a><a id="16562" class="Symbol">)</a> <a id="16564" href="plfa.part2.Lambda.html#14936" class="Function Operator">[</a> <a id="16566" class="String">&quot;y&quot;</a> <a id="16570" href="plfa.part2.Lambda.html#14936" class="Function Operator">:=</a> <a id="16573" href="plfa.part2.Lambda.html#3906" class="InductiveConstructor">`zero</a> <a id="16579" href="plfa.part2.Lambda.html#14936" class="Function Operator">]</a> <a id="16581" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="16583" href="plfa.part2.Lambda.html#3812" class="InductiveConstructor Operator">ƛ</a> <a id="16585" class="String">&quot;x&quot;</a> <a id="16589" href="plfa.part2.Lambda.html#3812" class="InductiveConstructor Operator">⇒</a> <a id="16591" href="plfa.part2.Lambda.html#3906" class="InductiveConstructor">`zero</a>
<a id="16597" class="Symbol">_</a> <a id="16599" class="Symbol">=</a> <a id="16601" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>

<a id="16607" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#16607" class="Function">_</a> <a id="16609" class="Symbol">:</a> <a id="16611" class="Symbol">(</a><a id="16612" href="plfa.part2.Lambda.html#3812" class="InductiveConstructor Operator">ƛ</a> <a id="16614" class="String">&quot;x&quot;</a> <a id="16618" href="plfa.part2.Lambda.html#3812" class="InductiveConstructor Operator">⇒</a> <a id="16620" href="plfa.part2.Lambda.html#3773" class="InductiveConstructor Operator">`</a> <a id="16622" class="String">&quot;x&quot;</a><a id="16625" class="Symbol">)</a> <a id="16627" href="plfa.part2.Lambda.html#14936" class="Function Operator">[</a> <a id="16629" class="String">&quot;x&quot;</a> <a id="16633" href="plfa.part2.Lambda.html#14936" class="Function Operator">:=</a> <a id="16636" href="plfa.part2.Lambda.html#3906" class="InductiveConstructor">`zero</a> <a id="16642" href="plfa.part2.Lambda.html#14936" class="Function Operator">]</a> <a id="16644" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="16646" href="plfa.part2.Lambda.html#3812" class="InductiveConstructor Operator">ƛ</a> <a id="16648" class="String">&quot;x&quot;</a> <a id="16652" href="plfa.part2.Lambda.html#3812" class="InductiveConstructor Operator">⇒</a> <a id="16654" href="plfa.part2.Lambda.html#3773" class="InductiveConstructor Operator">`</a> <a id="16656" class="String">&quot;x&quot;</a>
<a id="16660" class="Symbol">_</a> <a id="16662" class="Symbol">=</a> <a id="16664" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>

<a id="16670" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#16670" class="Function">_</a> <a id="16672" class="Symbol">:</a> <a id="16674" class="Symbol">(</a><a id="16675" href="plfa.part2.Lambda.html#3812" class="InductiveConstructor Operator">ƛ</a> <a id="16677" class="String">&quot;y&quot;</a> <a id="16681" href="plfa.part2.Lambda.html#3812" class="InductiveConstructor Operator">⇒</a> <a id="16683" href="plfa.part2.Lambda.html#3773" class="InductiveConstructor Operator">`</a> <a id="16685" class="String">&quot;y&quot;</a><a id="16688" class="Symbol">)</a> <a id="16690" href="plfa.part2.Lambda.html#14936" class="Function Operator">[</a> <a id="16692" class="String">&quot;x&quot;</a> <a id="16696" href="plfa.part2.Lambda.html#14936" class="Function Operator">:=</a> <a id="16699" href="plfa.part2.Lambda.html#3906" class="InductiveConstructor">`zero</a> <a id="16705" href="plfa.part2.Lambda.html#14936" class="Function Operator">]</a> <a id="16707" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="16709" href="plfa.part2.Lambda.html#3812" class="InductiveConstructor Operator">ƛ</a> <a id="16711" class="String">&quot;y&quot;</a> <a id="16715" href="plfa.part2.Lambda.html#3812" class="InductiveConstructor Operator">⇒</a> <a id="16717" href="plfa.part2.Lambda.html#3773" class="InductiveConstructor Operator">`</a> <a id="16719" class="String">&quot;y&quot;</a>
<a id="16723" class="Symbol">_</a> <a id="16725" class="Symbol">=</a> <a id="16727" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>
</pre>{% endraw %}

#### Quiz

What is the result of the following substitution?

    (ƛ "y" ⇒ ` "x" · (ƛ "x" ⇒ ` "x")) [ "x" := `zero ]

1. `` (ƛ "y" ⇒ ` "x" · (ƛ "x" ⇒ ` "x")) ``
2. `` (ƛ "y" ⇒ ` "x" · (ƛ "x" ⇒ `zero)) ``
3. `` (ƛ "y" ⇒ `zero · (ƛ "x" ⇒ ` "x")) ``
4. `` (ƛ "y" ⇒ `zero · (ƛ "x" ⇒ `zero)) ``


#### Exercise `_[_:=_]′` (stretch)

The definition of substitution above has three clauses (`ƛ`, `case`,
and `μ`) that invoke a `with` clause to deal with bound variables.
Rewrite the definition to factor the common part of these three
clauses into a single function, defined by mutual recursion with
substitution.

{% raw %}<pre class="Agda"><a id="17350" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}

## Reduction

We give the reduction rules for call-by-value lambda calculus.  To
reduce an application, first we reduce the left-hand side until it
becomes a value (which must be an abstraction); then we reduce the
right-hand side until it becomes a value; and finally we substitute
the argument for the variable in the abstraction.

In an informal presentation of the operational semantics,
the rules for reduction of applications are written as follows:

    L —→ L′
    --------------- ξ-·₁
    L · M —→ L′ · M

    M —→ M′
    --------------- ξ-·₂
    V · M —→ V · M′

    ----------------------------- β-ƛ
    (ƛ x ⇒ N) · V —→ N [ x := V ]

The Agda version of the rules below will be similar, except that universal
quantifications are made explicit, and so are the predicates that indicate
which terms are values.

The rules break into two sorts. Compatibility rules direct us to
reduce some part of a term.  We give them names starting with the
Greek letter `ξ` (_xi_).  Once a term is sufficiently reduced, it will
consist of a constructor and a deconstructor, in our case `ƛ` and `·`,
which reduces directly.  We give them names starting with the Greek
letter `β` (_beta_) and such rules are traditionally called _beta rules_.

A bit of terminology: A term that matches the left-hand side of a
reduction rule is called a _redex_. In the redex `(ƛ x ⇒ N) · V`, we
may refer to `x` as the _formal parameter_ of the function, and `V`
as the _actual parameter_ of the function application.  Beta reduction
replaces the formal parameter by the actual parameter.

If a term is a value, then no reduction applies; conversely,
if a reduction applies to a term then it is not a value.
We will show in the next chapter that 
this exhausts the possibilities: every well-typed term
either reduces or is a value.

For numbers, zero does not reduce and successor reduces the subterm.
A case expression reduces its argument to a number, and then chooses
the zero or successor branch as appropriate.  A fixpoint replaces
the bound variable by the entire fixpoint term; this is the one
case where we substitute by a term that is not a value.

Here are the rules formalised in Agda:

{% raw %}<pre class="Agda"><a id="19558" class="Keyword">infix</a> <a id="19564" class="Number">4</a> <a id="19566" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#19577" class="Datatype Operator">_—→_</a>

<a id="19572" class="Keyword">data</a> <a id="_—→_"></a><a id="19577" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#19577" class="Datatype Operator">_—→_</a> <a id="19582" class="Symbol">:</a> <a id="19584" href="plfa.part2.Lambda.html#3754" class="Datatype">Term</a> <a id="19589" class="Symbol">→</a> <a id="19591" href="plfa.part2.Lambda.html#3754" class="Datatype">Term</a> <a id="19596" class="Symbol">→</a> <a id="19598" class="PrimitiveType">Set</a> <a id="19602" class="Keyword">where</a>

  <a id="_—→_.ξ-·₁"></a><a id="19611" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#19611" class="InductiveConstructor">ξ-·₁</a> <a id="19616" class="Symbol">:</a> <a id="19618" class="Symbol">∀</a> <a id="19620" class="Symbol">{</a><a id="19621" href="plfa.part2.Lambda.html#19621" class="Bound">L</a> <a id="19623" href="plfa.part2.Lambda.html#19623" class="Bound">L′</a> <a id="19626" href="plfa.part2.Lambda.html#19626" class="Bound">M</a><a id="19627" class="Symbol">}</a>
    <a id="19633" class="Symbol">→</a> <a id="19635" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#19621" class="Bound">L</a> <a id="19637" href="plfa.part2.Lambda.html#19577" class="Datatype Operator">—→</a> <a id="19640" href="plfa.part2.Lambda.html#19623" class="Bound">L′</a>
      <a id="19649" class="Comment">-----------------</a>
    <a id="19671" class="Symbol">→</a> <a id="19673" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#19621" class="Bound">L</a> <a id="19675" href="plfa.part2.Lambda.html#3858" class="InductiveConstructor Operator">·</a> <a id="19677" href="plfa.part2.Lambda.html#19626" class="Bound">M</a> <a id="19679" href="plfa.part2.Lambda.html#19577" class="Datatype Operator">—→</a> <a id="19682" href="plfa.part2.Lambda.html#19623" class="Bound">L′</a> <a id="19685" href="plfa.part2.Lambda.html#3858" class="InductiveConstructor Operator">·</a> <a id="19687" href="plfa.part2.Lambda.html#19626" class="Bound">M</a>

  <a id="_—→_.ξ-·₂"></a><a id="19692" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#19692" class="InductiveConstructor">ξ-·₂</a> <a id="19697" class="Symbol">:</a> <a id="19699" class="Symbol">∀</a> <a id="19701" class="Symbol">{</a><a id="19702" href="plfa.part2.Lambda.html#19702" class="Bound">V</a> <a id="19704" href="plfa.part2.Lambda.html#19704" class="Bound">M</a> <a id="19706" href="plfa.part2.Lambda.html#19706" class="Bound">M′</a><a id="19708" class="Symbol">}</a>
    <a id="19714" class="Symbol">→</a> <a id="19716" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#11553" class="Datatype">Value</a> <a id="19722" href="plfa.part2.Lambda.html#19702" class="Bound">V</a>
    <a id="19728" class="Symbol">→</a> <a id="19730" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#19704" class="Bound">M</a> <a id="19732" href="plfa.part2.Lambda.html#19577" class="Datatype Operator">—→</a> <a id="19735" href="plfa.part2.Lambda.html#19706" class="Bound">M′</a>
      <a id="19744" class="Comment">-----------------</a>
    <a id="19766" class="Symbol">→</a> <a id="19768" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#19702" class="Bound">V</a> <a id="19770" href="plfa.part2.Lambda.html#3858" class="InductiveConstructor Operator">·</a> <a id="19772" href="plfa.part2.Lambda.html#19704" class="Bound">M</a> <a id="19774" href="plfa.part2.Lambda.html#19577" class="Datatype Operator">—→</a> <a id="19777" href="plfa.part2.Lambda.html#19702" class="Bound">V</a> <a id="19779" href="plfa.part2.Lambda.html#3858" class="InductiveConstructor Operator">·</a> <a id="19781" href="plfa.part2.Lambda.html#19706" class="Bound">M′</a>

  <a id="_—→_.β-ƛ"></a><a id="19787" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#19787" class="InductiveConstructor">β-ƛ</a> <a id="19791" class="Symbol">:</a> <a id="19793" class="Symbol">∀</a> <a id="19795" class="Symbol">{</a><a id="19796" href="plfa.part2.Lambda.html#19796" class="Bound">x</a> <a id="19798" href="plfa.part2.Lambda.html#19798" class="Bound">N</a> <a id="19800" href="plfa.part2.Lambda.html#19800" class="Bound">V</a><a id="19801" class="Symbol">}</a>
    <a id="19807" class="Symbol">→</a> <a id="19809" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#11553" class="Datatype">Value</a> <a id="19815" href="plfa.part2.Lambda.html#19800" class="Bound">V</a>
      <a id="19823" class="Comment">------------------------------</a>
    <a id="19858" class="Symbol">→</a> <a id="19860" class="Symbol">(</a><a id="19861" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3812" class="InductiveConstructor Operator">ƛ</a> <a id="19863" href="plfa.part2.Lambda.html#19796" class="Bound">x</a> <a id="19865" href="plfa.part2.Lambda.html#3812" class="InductiveConstructor Operator">⇒</a> <a id="19867" href="plfa.part2.Lambda.html#19798" class="Bound">N</a><a id="19868" class="Symbol">)</a> <a id="19870" href="plfa.part2.Lambda.html#3858" class="InductiveConstructor Operator">·</a> <a id="19872" href="plfa.part2.Lambda.html#19800" class="Bound">V</a> <a id="19874" href="plfa.part2.Lambda.html#19577" class="Datatype Operator">—→</a> <a id="19877" href="plfa.part2.Lambda.html#19798" class="Bound">N</a> <a id="19879" href="plfa.part2.Lambda.html#14936" class="Function Operator">[</a> <a id="19881" href="plfa.part2.Lambda.html#19796" class="Bound">x</a> <a id="19883" href="plfa.part2.Lambda.html#14936" class="Function Operator">:=</a> <a id="19886" href="plfa.part2.Lambda.html#19800" class="Bound">V</a> <a id="19888" href="plfa.part2.Lambda.html#14936" class="Function Operator">]</a>

  <a id="_—→_.ξ-suc"></a><a id="19893" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#19893" class="InductiveConstructor">ξ-suc</a> <a id="19899" class="Symbol">:</a> <a id="19901" class="Symbol">∀</a> <a id="19903" class="Symbol">{</a><a id="19904" href="plfa.part2.Lambda.html#19904" class="Bound">M</a> <a id="19906" href="plfa.part2.Lambda.html#19906" class="Bound">M′</a><a id="19908" class="Symbol">}</a>
    <a id="19914" class="Symbol">→</a> <a id="19916" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#19904" class="Bound">M</a> <a id="19918" href="plfa.part2.Lambda.html#19577" class="Datatype Operator">—→</a> <a id="19921" href="plfa.part2.Lambda.html#19906" class="Bound">M′</a>
      <a id="19930" class="Comment">------------------</a>
    <a id="19953" class="Symbol">→</a> <a id="19955" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3940" class="InductiveConstructor Operator">`suc</a> <a id="19960" href="plfa.part2.Lambda.html#19904" class="Bound">M</a> <a id="19962" href="plfa.part2.Lambda.html#19577" class="Datatype Operator">—→</a> <a id="19965" href="plfa.part2.Lambda.html#3940" class="InductiveConstructor Operator">`suc</a> <a id="19970" href="plfa.part2.Lambda.html#19906" class="Bound">M′</a>

  <a id="_—→_.ξ-case"></a><a id="19976" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#19976" class="InductiveConstructor">ξ-case</a> <a id="19983" class="Symbol">:</a> <a id="19985" class="Symbol">∀</a> <a id="19987" class="Symbol">{</a><a id="19988" href="plfa.part2.Lambda.html#19988" class="Bound">x</a> <a id="19990" href="plfa.part2.Lambda.html#19990" class="Bound">L</a> <a id="19992" href="plfa.part2.Lambda.html#19992" class="Bound">L′</a> <a id="19995" href="plfa.part2.Lambda.html#19995" class="Bound">M</a> <a id="19997" href="plfa.part2.Lambda.html#19997" class="Bound">N</a><a id="19998" class="Symbol">}</a>
    <a id="20004" class="Symbol">→</a> <a id="20006" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#19990" class="Bound">L</a> <a id="20008" href="plfa.part2.Lambda.html#19577" class="Datatype Operator">—→</a> <a id="20011" href="plfa.part2.Lambda.html#19992" class="Bound">L′</a>
      <a id="20020" class="Comment">-----------------------------------------------------------------</a>
    <a id="20090" class="Symbol">→</a> <a id="20092" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3981" class="InductiveConstructor Operator">case</a> <a id="20097" href="plfa.part2.Lambda.html#19990" class="Bound">L</a> <a id="20099" href="plfa.part2.Lambda.html#3981" class="InductiveConstructor Operator">[zero⇒</a> <a id="20106" href="plfa.part2.Lambda.html#19995" class="Bound">M</a> <a id="20108" href="plfa.part2.Lambda.html#3981" class="InductiveConstructor Operator">|suc</a> <a id="20113" href="plfa.part2.Lambda.html#19988" class="Bound">x</a> <a id="20115" href="plfa.part2.Lambda.html#3981" class="InductiveConstructor Operator">⇒</a> <a id="20117" href="plfa.part2.Lambda.html#19997" class="Bound">N</a> <a id="20119" href="plfa.part2.Lambda.html#3981" class="InductiveConstructor Operator">]</a> <a id="20121" href="plfa.part2.Lambda.html#19577" class="Datatype Operator">—→</a> <a id="20124" href="plfa.part2.Lambda.html#3981" class="InductiveConstructor Operator">case</a> <a id="20129" href="plfa.part2.Lambda.html#19992" class="Bound">L′</a> <a id="20132" href="plfa.part2.Lambda.html#3981" class="InductiveConstructor Operator">[zero⇒</a> <a id="20139" href="plfa.part2.Lambda.html#19995" class="Bound">M</a> <a id="20141" href="plfa.part2.Lambda.html#3981" class="InductiveConstructor Operator">|suc</a> <a id="20146" href="plfa.part2.Lambda.html#19988" class="Bound">x</a> <a id="20148" href="plfa.part2.Lambda.html#3981" class="InductiveConstructor Operator">⇒</a> <a id="20150" href="plfa.part2.Lambda.html#19997" class="Bound">N</a> <a id="20152" href="plfa.part2.Lambda.html#3981" class="InductiveConstructor Operator">]</a>

  <a id="_—→_.β-zero"></a><a id="20157" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#20157" class="InductiveConstructor">β-zero</a> <a id="20164" class="Symbol">:</a> <a id="20166" class="Symbol">∀</a> <a id="20168" class="Symbol">{</a><a id="20169" href="plfa.part2.Lambda.html#20169" class="Bound">x</a> <a id="20171" href="plfa.part2.Lambda.html#20171" class="Bound">M</a> <a id="20173" href="plfa.part2.Lambda.html#20173" class="Bound">N</a><a id="20174" class="Symbol">}</a>
      <a id="20182" class="Comment">----------------------------------------</a>
    <a id="20227" class="Symbol">→</a> <a id="20229" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3981" class="InductiveConstructor Operator">case</a> <a id="20234" href="plfa.part2.Lambda.html#3906" class="InductiveConstructor">`zero</a> <a id="20240" href="plfa.part2.Lambda.html#3981" class="InductiveConstructor Operator">[zero⇒</a> <a id="20247" href="plfa.part2.Lambda.html#20171" class="Bound">M</a> <a id="20249" href="plfa.part2.Lambda.html#3981" class="InductiveConstructor Operator">|suc</a> <a id="20254" href="plfa.part2.Lambda.html#20169" class="Bound">x</a> <a id="20256" href="plfa.part2.Lambda.html#3981" class="InductiveConstructor Operator">⇒</a> <a id="20258" href="plfa.part2.Lambda.html#20173" class="Bound">N</a> <a id="20260" href="plfa.part2.Lambda.html#3981" class="InductiveConstructor Operator">]</a> <a id="20262" href="plfa.part2.Lambda.html#19577" class="Datatype Operator">—→</a> <a id="20265" href="plfa.part2.Lambda.html#20171" class="Bound">M</a>

  <a id="_—→_.β-suc"></a><a id="20270" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#20270" class="InductiveConstructor">β-suc</a> <a id="20276" class="Symbol">:</a> <a id="20278" class="Symbol">∀</a> <a id="20280" class="Symbol">{</a><a id="20281" href="plfa.part2.Lambda.html#20281" class="Bound">x</a> <a id="20283" href="plfa.part2.Lambda.html#20283" class="Bound">V</a> <a id="20285" href="plfa.part2.Lambda.html#20285" class="Bound">M</a> <a id="20287" href="plfa.part2.Lambda.html#20287" class="Bound">N</a><a id="20288" class="Symbol">}</a>
    <a id="20294" class="Symbol">→</a> <a id="20296" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#11553" class="Datatype">Value</a> <a id="20302" href="plfa.part2.Lambda.html#20283" class="Bound">V</a>
      <a id="20310" class="Comment">---------------------------------------------------</a>
    <a id="20366" class="Symbol">→</a> <a id="20368" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3981" class="InductiveConstructor Operator">case</a> <a id="20373" href="plfa.part2.Lambda.html#3940" class="InductiveConstructor Operator">`suc</a> <a id="20378" href="plfa.part2.Lambda.html#20283" class="Bound">V</a> <a id="20380" href="plfa.part2.Lambda.html#3981" class="InductiveConstructor Operator">[zero⇒</a> <a id="20387" href="plfa.part2.Lambda.html#20285" class="Bound">M</a> <a id="20389" href="plfa.part2.Lambda.html#3981" class="InductiveConstructor Operator">|suc</a> <a id="20394" href="plfa.part2.Lambda.html#20281" class="Bound">x</a> <a id="20396" href="plfa.part2.Lambda.html#3981" class="InductiveConstructor Operator">⇒</a> <a id="20398" href="plfa.part2.Lambda.html#20287" class="Bound">N</a> <a id="20400" href="plfa.part2.Lambda.html#3981" class="InductiveConstructor Operator">]</a> <a id="20402" href="plfa.part2.Lambda.html#19577" class="Datatype Operator">—→</a> <a id="20405" href="plfa.part2.Lambda.html#20287" class="Bound">N</a> <a id="20407" href="plfa.part2.Lambda.html#14936" class="Function Operator">[</a> <a id="20409" href="plfa.part2.Lambda.html#20281" class="Bound">x</a> <a id="20411" href="plfa.part2.Lambda.html#14936" class="Function Operator">:=</a> <a id="20414" href="plfa.part2.Lambda.html#20283" class="Bound">V</a> <a id="20416" href="plfa.part2.Lambda.html#14936" class="Function Operator">]</a>

  <a id="_—→_.β-μ"></a><a id="20421" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#20421" class="InductiveConstructor">β-μ</a> <a id="20425" class="Symbol">:</a> <a id="20427" class="Symbol">∀</a> <a id="20429" class="Symbol">{</a><a id="20430" href="plfa.part2.Lambda.html#20430" class="Bound">x</a> <a id="20432" href="plfa.part2.Lambda.html#20432" class="Bound">M</a><a id="20433" class="Symbol">}</a>
      <a id="20441" class="Comment">------------------------------</a>
    <a id="20476" class="Symbol">→</a> <a id="20478" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#4041" class="InductiveConstructor Operator">μ</a> <a id="20480" href="plfa.part2.Lambda.html#20430" class="Bound">x</a> <a id="20482" href="plfa.part2.Lambda.html#4041" class="InductiveConstructor Operator">⇒</a> <a id="20484" href="plfa.part2.Lambda.html#20432" class="Bound">M</a> <a id="20486" href="plfa.part2.Lambda.html#19577" class="Datatype Operator">—→</a> <a id="20489" href="plfa.part2.Lambda.html#20432" class="Bound">M</a> <a id="20491" href="plfa.part2.Lambda.html#14936" class="Function Operator">[</a> <a id="20493" href="plfa.part2.Lambda.html#20430" class="Bound">x</a> <a id="20495" href="plfa.part2.Lambda.html#14936" class="Function Operator">:=</a> <a id="20498" href="plfa.part2.Lambda.html#4041" class="InductiveConstructor Operator">μ</a> <a id="20500" href="plfa.part2.Lambda.html#20430" class="Bound">x</a> <a id="20502" href="plfa.part2.Lambda.html#4041" class="InductiveConstructor Operator">⇒</a> <a id="20504" href="plfa.part2.Lambda.html#20432" class="Bound">M</a> <a id="20506" href="plfa.part2.Lambda.html#14936" class="Function Operator">]</a>
</pre>{% endraw %}
The reduction rules are carefully designed to ensure that subterms
of a term are reduced to values before the whole term is reduced.
This is referred to as _call-by-value_ reduction.

Further, we have arranged that subterms are reduced in a
left-to-right order.  This means that reduction is _deterministic_:
for any term, there is at most one other term to which it reduces.
Put another way, our reduction relation `—→` is in fact a function.

This style of explaining the meaning of terms is called
a _small-step operational semantics_.  If `M —→ N`, we say that
term `M` _reduces_ to term `N`, or equivalently,
term `M` _steps_ to term `N`.  Each compatibility rule has
another reduction rule in its premise; so a step always consists
of a beta rule, possibly adjusted by zero or more compatibility rules.


#### Quiz

What does the following term step to?

    (ƛ "x" ⇒ ` "x") · (ƛ "x" ⇒ ` "x")  —→  ???

1.  `` (ƛ "x" ⇒ ` "x") ``
2.  `` (ƛ "x" ⇒ ` "x") · (ƛ "x" ⇒ ` "x") ``
3.  `` (ƛ "x" ⇒ ` "x") · (ƛ "x" ⇒ ` "x") · (ƛ "x" ⇒ ` "x") ``

What does the following term step to?

    (ƛ "x" ⇒ ` "x") · (ƛ "x" ⇒ ` "x") · (ƛ "x" ⇒ ` "x")  —→  ???

1.  `` (ƛ "x" ⇒ ` "x") ``
2.  `` (ƛ "x" ⇒ ` "x") · (ƛ "x" ⇒ ` "x") ``
3.  `` (ƛ "x" ⇒ ` "x") · (ƛ "x" ⇒ ` "x") · (ƛ "x" ⇒ ` "x") ``

What does the following term step to?  (Where `twoᶜ` and `sucᶜ` are as
defined above.)

    twoᶜ · sucᶜ · `zero  —→  ???

1.  `` sucᶜ · (sucᶜ · `zero) ``
2.  `` (ƛ "z" ⇒ sucᶜ · (sucᶜ · ` "z")) · `zero ``
3.  `` `zero ``


## Reflexive and transitive closure

A single step is only part of the story. In general, we wish to repeatedly
step a closed term until it reduces to a value.  We do this by defining
the reflexive and transitive closure `—↠` of the step relation `—→`.

We define reflexive and transitive closure as a sequence of zero or
more steps of the underlying relation, along lines similar to that for
reasoning about chains of equalities in
Chapter [Equality]({{ site.baseurl }}/Equality/):
{% raw %}<pre class="Agda"><a id="22502" class="Keyword">infix</a>  <a id="22509" class="Number">2</a> <a id="22511" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#22567" class="Datatype Operator">_—↠_</a>
<a id="22516" class="Keyword">infix</a>  <a id="22523" class="Number">1</a> <a id="22525" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#22717" class="Function Operator">begin_</a>
<a id="22532" class="Keyword">infixr</a> <a id="22539" class="Number">2</a> <a id="22541" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#22641" class="InductiveConstructor Operator">_—→⟨_⟩_</a>
<a id="22549" class="Keyword">infix</a>  <a id="22556" class="Number">3</a> <a id="22558" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#22600" class="InductiveConstructor Operator">_∎</a>

<a id="22562" class="Keyword">data</a> <a id="_—↠_"></a><a id="22567" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#22567" class="Datatype Operator">_—↠_</a> <a id="22572" class="Symbol">:</a> <a id="22574" href="plfa.part2.Lambda.html#3754" class="Datatype">Term</a> <a id="22579" class="Symbol">→</a> <a id="22581" href="plfa.part2.Lambda.html#3754" class="Datatype">Term</a> <a id="22586" class="Symbol">→</a> <a id="22588" class="PrimitiveType">Set</a> <a id="22592" class="Keyword">where</a>
  <a id="_—↠_._∎"></a><a id="22600" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#22600" class="InductiveConstructor Operator">_∎</a> <a id="22603" class="Symbol">:</a> <a id="22605" class="Symbol">∀</a> <a id="22607" href="plfa.part2.Lambda.html#22607" class="Bound">M</a>
      <a id="22615" class="Comment">---------</a>
    <a id="22629" class="Symbol">→</a> <a id="22631" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#22607" class="Bound">M</a> <a id="22633" href="plfa.part2.Lambda.html#22567" class="Datatype Operator">—↠</a> <a id="22636" href="plfa.part2.Lambda.html#22607" class="Bound">M</a>

  <a id="_—↠_._—→⟨_⟩_"></a><a id="22641" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#22641" class="InductiveConstructor Operator">_—→⟨_⟩_</a> <a id="22649" class="Symbol">:</a> <a id="22651" class="Symbol">∀</a> <a id="22653" href="plfa.part2.Lambda.html#22653" class="Bound">L</a> <a id="22655" class="Symbol">{</a><a id="22656" href="plfa.part2.Lambda.html#22656" class="Bound">M</a> <a id="22658" href="plfa.part2.Lambda.html#22658" class="Bound">N</a><a id="22659" class="Symbol">}</a>
    <a id="22665" class="Symbol">→</a> <a id="22667" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#22653" class="Bound">L</a> <a id="22669" href="plfa.part2.Lambda.html#19577" class="Datatype Operator">—→</a> <a id="22672" href="plfa.part2.Lambda.html#22656" class="Bound">M</a>
    <a id="22678" class="Symbol">→</a> <a id="22680" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#22656" class="Bound">M</a> <a id="22682" href="plfa.part2.Lambda.html#22567" class="Datatype Operator">—↠</a> <a id="22685" href="plfa.part2.Lambda.html#22658" class="Bound">N</a>
      <a id="22693" class="Comment">---------</a>
    <a id="22707" class="Symbol">→</a> <a id="22709" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#22653" class="Bound">L</a> <a id="22711" href="plfa.part2.Lambda.html#22567" class="Datatype Operator">—↠</a> <a id="22714" href="plfa.part2.Lambda.html#22658" class="Bound">N</a>

<a id="begin_"></a><a id="22717" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#22717" class="Function Operator">begin_</a> <a id="22724" class="Symbol">:</a> <a id="22726" class="Symbol">∀</a> <a id="22728" class="Symbol">{</a><a id="22729" href="plfa.part2.Lambda.html#22729" class="Bound">M</a> <a id="22731" href="plfa.part2.Lambda.html#22731" class="Bound">N</a><a id="22732" class="Symbol">}</a>
  <a id="22736" class="Symbol">→</a> <a id="22738" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#22729" class="Bound">M</a> <a id="22740" href="plfa.part2.Lambda.html#22567" class="Datatype Operator">—↠</a> <a id="22743" href="plfa.part2.Lambda.html#22731" class="Bound">N</a>
    <a id="22749" class="Comment">------</a>
  <a id="22758" class="Symbol">→</a> <a id="22760" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#22729" class="Bound">M</a> <a id="22762" href="plfa.part2.Lambda.html#22567" class="Datatype Operator">—↠</a> <a id="22765" href="plfa.part2.Lambda.html#22731" class="Bound">N</a>
<a id="22767" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#22717" class="Function Operator">begin</a> <a id="22773" href="plfa.part2.Lambda.html#22773" class="Bound">M—↠N</a> <a id="22778" class="Symbol">=</a> <a id="22780" href="plfa.part2.Lambda.html#22773" class="Bound">M—↠N</a>
</pre>{% endraw %}We can read this as follows:

* From term `M`, we can take no steps, giving a step of type `M —↠ M`.
  It is written `M ∎`.

* From term `L` we can take a single step of type `L —→ M` followed by zero
  or more steps of type `M —↠ N`, giving a step of type `L —↠ N`. It is
  written `L —→⟨ L—→M ⟩ M—↠N`, where `L—→M` and `M—↠N` are steps of the
  appropriate type.

The notation is chosen to allow us to lay out example reductions in an
appealing way, as we will see in the next section.

An alternative is to define reflexive and transitive closure directly,
as the smallest relation that includes `—→` and is also reflexive
and transitive.  We could do so as follows:
{% raw %}<pre class="Agda"><a id="23463" class="Keyword">data</a> <a id="_—↠′_"></a><a id="23468" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23468" class="Datatype Operator">_—↠′_</a> <a id="23474" class="Symbol">:</a> <a id="23476" href="plfa.part2.Lambda.html#3754" class="Datatype">Term</a> <a id="23481" class="Symbol">→</a> <a id="23483" href="plfa.part2.Lambda.html#3754" class="Datatype">Term</a> <a id="23488" class="Symbol">→</a> <a id="23490" class="PrimitiveType">Set</a> <a id="23494" class="Keyword">where</a>

  <a id="_—↠′_.step′"></a><a id="23503" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23503" class="InductiveConstructor">step′</a> <a id="23509" class="Symbol">:</a> <a id="23511" class="Symbol">∀</a> <a id="23513" class="Symbol">{</a><a id="23514" href="plfa.part2.Lambda.html#23514" class="Bound">M</a> <a id="23516" href="plfa.part2.Lambda.html#23516" class="Bound">N</a><a id="23517" class="Symbol">}</a>
    <a id="23523" class="Symbol">→</a> <a id="23525" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23514" class="Bound">M</a> <a id="23527" href="plfa.part2.Lambda.html#19577" class="Datatype Operator">—→</a> <a id="23530" href="plfa.part2.Lambda.html#23516" class="Bound">N</a>
      <a id="23538" class="Comment">-------</a>
    <a id="23550" class="Symbol">→</a> <a id="23552" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23514" class="Bound">M</a> <a id="23554" href="plfa.part2.Lambda.html#23468" class="Datatype Operator">—↠′</a> <a id="23558" href="plfa.part2.Lambda.html#23516" class="Bound">N</a>

  <a id="_—↠′_.refl′"></a><a id="23563" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23563" class="InductiveConstructor">refl′</a> <a id="23569" class="Symbol">:</a> <a id="23571" class="Symbol">∀</a> <a id="23573" class="Symbol">{</a><a id="23574" href="plfa.part2.Lambda.html#23574" class="Bound">M</a><a id="23575" class="Symbol">}</a>
      <a id="23583" class="Comment">-------</a>
    <a id="23595" class="Symbol">→</a> <a id="23597" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23574" class="Bound">M</a> <a id="23599" href="plfa.part2.Lambda.html#23468" class="Datatype Operator">—↠′</a> <a id="23603" href="plfa.part2.Lambda.html#23574" class="Bound">M</a>

  <a id="_—↠′_.trans′"></a><a id="23608" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23608" class="InductiveConstructor">trans′</a> <a id="23615" class="Symbol">:</a> <a id="23617" class="Symbol">∀</a> <a id="23619" class="Symbol">{</a><a id="23620" href="plfa.part2.Lambda.html#23620" class="Bound">L</a> <a id="23622" href="plfa.part2.Lambda.html#23622" class="Bound">M</a> <a id="23624" href="plfa.part2.Lambda.html#23624" class="Bound">N</a><a id="23625" class="Symbol">}</a>
    <a id="23631" class="Symbol">→</a> <a id="23633" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23620" class="Bound">L</a> <a id="23635" href="plfa.part2.Lambda.html#23468" class="Datatype Operator">—↠′</a> <a id="23639" href="plfa.part2.Lambda.html#23622" class="Bound">M</a>
    <a id="23645" class="Symbol">→</a> <a id="23647" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23622" class="Bound">M</a> <a id="23649" href="plfa.part2.Lambda.html#23468" class="Datatype Operator">—↠′</a> <a id="23653" href="plfa.part2.Lambda.html#23624" class="Bound">N</a>
      <a id="23661" class="Comment">-------</a>
    <a id="23673" class="Symbol">→</a> <a id="23675" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23620" class="Bound">L</a> <a id="23677" href="plfa.part2.Lambda.html#23468" class="Datatype Operator">—↠′</a> <a id="23681" href="plfa.part2.Lambda.html#23624" class="Bound">N</a>
</pre>{% endraw %}The three constructors specify, respectively, that `—↠′` includes `—→`
and is reflexive and transitive.  A good exercise is to show that
the two definitions are equivalent (indeed, one embeds in the other).

#### Exercise `—↠≲—↠′` (practice)

Show that the first notion of reflexive and transitive closure
above embeds into the second. Why are they not isomorphic?

{% raw %}<pre class="Agda"><a id="24057" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}
## Confluence

One important property a reduction relation might satisfy is
to be _confluent_.  If term `L` reduces to two other terms,
`M` and `N`, then both of these reduce to a common term `P`.
It can be illustrated as follows:

               L
              / \
             /   \
            /     \
           M       N
            \     /
             \   /
              \ /
               P

Here `L`, `M`, `N` are universally quantified while `P`
is existentially quantified.  If each line stands for zero
or more reduction steps, this is called confluence,
while if the top two lines stand for a single reduction
step and the bottom two stand for zero or more reduction
steps it is called the diamond property. In symbols:

    confluence : ∀ {L M N} → ∃[ P ]
      ( ((L —↠ M) × (L —↠ N))
        --------------------
      → ((M —↠ P) × (N —↠ P)) )

    diamond : ∀ {L M N} → ∃[ P ]
      ( ((L —→ M) × (L —→ N))
        --------------------
      → ((M —↠ P) × (N —↠ P)) )

The reduction system studied in this chapter is deterministic.
In symbols:

    deterministic : ∀ {L M N}
      → L —→ M
      → L —→ N
        ------
      → M ≡ N

It is easy to show that every deterministic relation satisfies
the diamond property, and that every relation that satisfies
the diamond property is confluent.  Hence, all the reduction
systems studied in this text are trivially confluent.


## Examples

We start with a simple example. The Church numeral two applied to the
successor function and zero yields the natural number two:
{% raw %}<pre class="Agda"><a id="25627" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#25627" class="Function">_</a> <a id="25629" class="Symbol">:</a> <a id="25631" href="plfa.part2.Lambda.html#5731" class="Function">twoᶜ</a> <a id="25636" href="plfa.part2.Lambda.html#3858" class="InductiveConstructor Operator">·</a> <a id="25638" href="plfa.part2.Lambda.html#5896" class="Function">sucᶜ</a> <a id="25643" href="plfa.part2.Lambda.html#3858" class="InductiveConstructor Operator">·</a> <a id="25645" href="plfa.part2.Lambda.html#3906" class="InductiveConstructor">`zero</a> <a id="25651" href="plfa.part2.Lambda.html#22567" class="Datatype Operator">—↠</a> <a id="25654" href="plfa.part2.Lambda.html#3940" class="InductiveConstructor Operator">`suc</a> <a id="25659" href="plfa.part2.Lambda.html#3940" class="InductiveConstructor Operator">`suc</a> <a id="25664" href="plfa.part2.Lambda.html#3906" class="InductiveConstructor">`zero</a>
<a id="25670" class="Symbol">_</a> <a id="25672" class="Symbol">=</a>
  <a id="25676" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#22717" class="Function Operator">begin</a>
    <a id="25686" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#5731" class="Function">twoᶜ</a> <a id="25691" href="plfa.part2.Lambda.html#3858" class="InductiveConstructor Operator">·</a> <a id="25693" href="plfa.part2.Lambda.html#5896" class="Function">sucᶜ</a> <a id="25698" href="plfa.part2.Lambda.html#3858" class="InductiveConstructor Operator">·</a> <a id="25700" href="plfa.part2.Lambda.html#3906" class="InductiveConstructor">`zero</a>
  <a id="25708" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#22641" class="InductiveConstructor Operator">—→⟨</a> <a id="25712" href="plfa.part2.Lambda.html#19611" class="InductiveConstructor">ξ-·₁</a> <a id="25717" class="Symbol">(</a><a id="25718" href="plfa.part2.Lambda.html#19787" class="InductiveConstructor">β-ƛ</a> <a id="25722" href="plfa.part2.Lambda.html#11581" class="InductiveConstructor">V-ƛ</a><a id="25725" class="Symbol">)</a> <a id="25727" href="plfa.part2.Lambda.html#22641" class="InductiveConstructor Operator">⟩</a>
    <a id="25733" class="Symbol">(</a><a id="25734" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3812" class="InductiveConstructor Operator">ƛ</a> <a id="25736" class="String">&quot;z&quot;</a> <a id="25740" href="plfa.part2.Lambda.html#3812" class="InductiveConstructor Operator">⇒</a> <a id="25742" href="plfa.part2.Lambda.html#5896" class="Function">sucᶜ</a> <a id="25747" href="plfa.part2.Lambda.html#3858" class="InductiveConstructor Operator">·</a> <a id="25749" class="Symbol">(</a><a id="25750" href="plfa.part2.Lambda.html#5896" class="Function">sucᶜ</a> <a id="25755" href="plfa.part2.Lambda.html#3858" class="InductiveConstructor Operator">·</a> <a id="25757" href="plfa.part2.Lambda.html#3773" class="InductiveConstructor Operator">`</a> <a id="25759" class="String">&quot;z&quot;</a><a id="25762" class="Symbol">))</a> <a id="25765" href="plfa.part2.Lambda.html#3858" class="InductiveConstructor Operator">·</a> <a id="25767" href="plfa.part2.Lambda.html#3906" class="InductiveConstructor">`zero</a>
  <a id="25775" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#22641" class="InductiveConstructor Operator">—→⟨</a> <a id="25779" href="plfa.part2.Lambda.html#19787" class="InductiveConstructor">β-ƛ</a> <a id="25783" href="plfa.part2.Lambda.html#11642" class="InductiveConstructor">V-zero</a> <a id="25790" href="plfa.part2.Lambda.html#22641" class="InductiveConstructor Operator">⟩</a>
    <a id="25796" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#5896" class="Function">sucᶜ</a> <a id="25801" href="plfa.part2.Lambda.html#3858" class="InductiveConstructor Operator">·</a> <a id="25803" class="Symbol">(</a><a id="25804" href="plfa.part2.Lambda.html#5896" class="Function">sucᶜ</a> <a id="25809" href="plfa.part2.Lambda.html#3858" class="InductiveConstructor Operator">·</a> <a id="25811" href="plfa.part2.Lambda.html#3906" class="InductiveConstructor">`zero</a><a id="25816" class="Symbol">)</a>
  <a id="25820" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#22641" class="InductiveConstructor Operator">—→⟨</a> <a id="25824" href="plfa.part2.Lambda.html#19692" class="InductiveConstructor">ξ-·₂</a> <a id="25829" href="plfa.part2.Lambda.html#11581" class="InductiveConstructor">V-ƛ</a> <a id="25833" class="Symbol">(</a><a id="25834" href="plfa.part2.Lambda.html#19787" class="InductiveConstructor">β-ƛ</a> <a id="25838" href="plfa.part2.Lambda.html#11642" class="InductiveConstructor">V-zero</a><a id="25844" class="Symbol">)</a> <a id="25846" href="plfa.part2.Lambda.html#22641" class="InductiveConstructor Operator">⟩</a>
    <a id="25852" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#5896" class="Function">sucᶜ</a> <a id="25857" href="plfa.part2.Lambda.html#3858" class="InductiveConstructor Operator">·</a> <a id="25859" href="plfa.part2.Lambda.html#3940" class="InductiveConstructor Operator">`suc</a> <a id="25864" href="plfa.part2.Lambda.html#3906" class="InductiveConstructor">`zero</a>
  <a id="25872" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#22641" class="InductiveConstructor Operator">—→⟨</a> <a id="25876" href="plfa.part2.Lambda.html#19787" class="InductiveConstructor">β-ƛ</a> <a id="25880" class="Symbol">(</a><a id="25881" href="plfa.part2.Lambda.html#11690" class="InductiveConstructor">V-suc</a> <a id="25887" href="plfa.part2.Lambda.html#11642" class="InductiveConstructor">V-zero</a><a id="25893" class="Symbol">)</a> <a id="25895" href="plfa.part2.Lambda.html#22641" class="InductiveConstructor Operator">⟩</a>
    <a id="25901" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3940" class="InductiveConstructor Operator">`suc</a> <a id="25906" class="Symbol">(</a><a id="25907" href="plfa.part2.Lambda.html#3940" class="InductiveConstructor Operator">`suc</a> <a id="25912" href="plfa.part2.Lambda.html#3906" class="InductiveConstructor">`zero</a><a id="25917" class="Symbol">)</a>
  <a id="25921" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#22600" class="InductiveConstructor Operator">∎</a>
</pre>{% endraw %}
Here is a sample reduction demonstrating that two plus two is four:
{% raw %}<pre class="Agda"><a id="26000" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#26000" class="Function">_</a> <a id="26002" class="Symbol">:</a> <a id="26004" href="plfa.part2.Lambda.html#4516" class="Function">plus</a> <a id="26009" href="plfa.part2.Lambda.html#3858" class="InductiveConstructor Operator">·</a> <a id="26011" href="plfa.part2.Lambda.html#4482" class="Function">two</a> <a id="26015" href="plfa.part2.Lambda.html#3858" class="InductiveConstructor Operator">·</a> <a id="26017" href="plfa.part2.Lambda.html#4482" class="Function">two</a> <a id="26021" href="plfa.part2.Lambda.html#22567" class="Datatype Operator">—↠</a> <a id="26024" href="plfa.part2.Lambda.html#3940" class="InductiveConstructor Operator">`suc</a> <a id="26029" href="plfa.part2.Lambda.html#3940" class="InductiveConstructor Operator">`suc</a> <a id="26034" href="plfa.part2.Lambda.html#3940" class="InductiveConstructor Operator">`suc</a> <a id="26039" href="plfa.part2.Lambda.html#3940" class="InductiveConstructor Operator">`suc</a> <a id="26044" href="plfa.part2.Lambda.html#3906" class="InductiveConstructor">`zero</a>
<a id="26050" class="Symbol">_</a> <a id="26052" class="Symbol">=</a>
  <a id="26056" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#22717" class="Function Operator">begin</a>
    <a id="26066" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#4516" class="Function">plus</a> <a id="26071" href="plfa.part2.Lambda.html#3858" class="InductiveConstructor Operator">·</a> <a id="26073" href="plfa.part2.Lambda.html#4482" class="Function">two</a> <a id="26077" href="plfa.part2.Lambda.html#3858" class="InductiveConstructor Operator">·</a> <a id="26079" href="plfa.part2.Lambda.html#4482" class="Function">two</a>
  <a id="26085" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#22641" class="InductiveConstructor Operator">—→⟨</a> <a id="26089" href="plfa.part2.Lambda.html#19611" class="InductiveConstructor">ξ-·₁</a> <a id="26094" class="Symbol">(</a><a id="26095" href="plfa.part2.Lambda.html#19611" class="InductiveConstructor">ξ-·₁</a> <a id="26100" href="plfa.part2.Lambda.html#20421" class="InductiveConstructor">β-μ</a><a id="26103" class="Symbol">)</a> <a id="26105" href="plfa.part2.Lambda.html#22641" class="InductiveConstructor Operator">⟩</a>
    <a id="26111" class="Symbol">(</a><a id="26112" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3812" class="InductiveConstructor Operator">ƛ</a> <a id="26114" class="String">&quot;m&quot;</a> <a id="26118" href="plfa.part2.Lambda.html#3812" class="InductiveConstructor Operator">⇒</a> <a id="26120" href="plfa.part2.Lambda.html#3812" class="InductiveConstructor Operator">ƛ</a> <a id="26122" class="String">&quot;n&quot;</a> <a id="26126" href="plfa.part2.Lambda.html#3812" class="InductiveConstructor Operator">⇒</a>
      <a id="26134" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3981" class="InductiveConstructor Operator">case</a> <a id="26139" href="plfa.part2.Lambda.html#3773" class="InductiveConstructor Operator">`</a> <a id="26141" class="String">&quot;m&quot;</a> <a id="26145" href="plfa.part2.Lambda.html#3981" class="InductiveConstructor Operator">[zero⇒</a> <a id="26152" href="plfa.part2.Lambda.html#3773" class="InductiveConstructor Operator">`</a> <a id="26154" class="String">&quot;n&quot;</a> <a id="26158" href="plfa.part2.Lambda.html#3981" class="InductiveConstructor Operator">|suc</a> <a id="26163" class="String">&quot;m&quot;</a> <a id="26167" href="plfa.part2.Lambda.html#3981" class="InductiveConstructor Operator">⇒</a> <a id="26169" href="plfa.part2.Lambda.html#3940" class="InductiveConstructor Operator">`suc</a> <a id="26174" class="Symbol">(</a><a id="26175" href="plfa.part2.Lambda.html#4516" class="Function">plus</a> <a id="26180" href="plfa.part2.Lambda.html#3858" class="InductiveConstructor Operator">·</a> <a id="26182" href="plfa.part2.Lambda.html#3773" class="InductiveConstructor Operator">`</a> <a id="26184" class="String">&quot;m&quot;</a> <a id="26188" href="plfa.part2.Lambda.html#3858" class="InductiveConstructor Operator">·</a> <a id="26190" href="plfa.part2.Lambda.html#3773" class="InductiveConstructor Operator">`</a> <a id="26192" class="String">&quot;n&quot;</a><a id="26195" class="Symbol">)</a> <a id="26197" href="plfa.part2.Lambda.html#3981" class="InductiveConstructor Operator">]</a><a id="26198" class="Symbol">)</a>
        <a id="26208" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3858" class="InductiveConstructor Operator">·</a> <a id="26210" href="plfa.part2.Lambda.html#4482" class="Function">two</a> <a id="26214" href="plfa.part2.Lambda.html#3858" class="InductiveConstructor Operator">·</a> <a id="26216" href="plfa.part2.Lambda.html#4482" class="Function">two</a>
  <a id="26222" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#22641" class="InductiveConstructor Operator">—→⟨</a> <a id="26226" href="plfa.part2.Lambda.html#19611" class="InductiveConstructor">ξ-·₁</a> <a id="26231" class="Symbol">(</a><a id="26232" href="plfa.part2.Lambda.html#19787" class="InductiveConstructor">β-ƛ</a> <a id="26236" class="Symbol">(</a><a id="26237" href="plfa.part2.Lambda.html#11690" class="InductiveConstructor">V-suc</a> <a id="26243" class="Symbol">(</a><a id="26244" href="plfa.part2.Lambda.html#11690" class="InductiveConstructor">V-suc</a> <a id="26250" href="plfa.part2.Lambda.html#11642" class="InductiveConstructor">V-zero</a><a id="26256" class="Symbol">)))</a> <a id="26260" href="plfa.part2.Lambda.html#22641" class="InductiveConstructor Operator">⟩</a>
    <a id="26266" class="Symbol">(</a><a id="26267" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3812" class="InductiveConstructor Operator">ƛ</a> <a id="26269" class="String">&quot;n&quot;</a> <a id="26273" href="plfa.part2.Lambda.html#3812" class="InductiveConstructor Operator">⇒</a>
      <a id="26281" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3981" class="InductiveConstructor Operator">case</a> <a id="26286" href="plfa.part2.Lambda.html#4482" class="Function">two</a> <a id="26290" href="plfa.part2.Lambda.html#3981" class="InductiveConstructor Operator">[zero⇒</a> <a id="26297" href="plfa.part2.Lambda.html#3773" class="InductiveConstructor Operator">`</a> <a id="26299" class="String">&quot;n&quot;</a> <a id="26303" href="plfa.part2.Lambda.html#3981" class="InductiveConstructor Operator">|suc</a> <a id="26308" class="String">&quot;m&quot;</a> <a id="26312" href="plfa.part2.Lambda.html#3981" class="InductiveConstructor Operator">⇒</a> <a id="26314" href="plfa.part2.Lambda.html#3940" class="InductiveConstructor Operator">`suc</a> <a id="26319" class="Symbol">(</a><a id="26320" href="plfa.part2.Lambda.html#4516" class="Function">plus</a> <a id="26325" href="plfa.part2.Lambda.html#3858" class="InductiveConstructor Operator">·</a> <a id="26327" href="plfa.part2.Lambda.html#3773" class="InductiveConstructor Operator">`</a> <a id="26329" class="String">&quot;m&quot;</a> <a id="26333" href="plfa.part2.Lambda.html#3858" class="InductiveConstructor Operator">·</a> <a id="26335" href="plfa.part2.Lambda.html#3773" class="InductiveConstructor Operator">`</a> <a id="26337" class="String">&quot;n&quot;</a><a id="26340" class="Symbol">)</a> <a id="26342" href="plfa.part2.Lambda.html#3981" class="InductiveConstructor Operator">]</a><a id="26343" class="Symbol">)</a>
         <a id="26354" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3858" class="InductiveConstructor Operator">·</a> <a id="26356" href="plfa.part2.Lambda.html#4482" class="Function">two</a>
  <a id="26362" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#22641" class="InductiveConstructor Operator">—→⟨</a> <a id="26366" href="plfa.part2.Lambda.html#19787" class="InductiveConstructor">β-ƛ</a> <a id="26370" class="Symbol">(</a><a id="26371" href="plfa.part2.Lambda.html#11690" class="InductiveConstructor">V-suc</a> <a id="26377" class="Symbol">(</a><a id="26378" href="plfa.part2.Lambda.html#11690" class="InductiveConstructor">V-suc</a> <a id="26384" href="plfa.part2.Lambda.html#11642" class="InductiveConstructor">V-zero</a><a id="26390" class="Symbol">))</a> <a id="26393" href="plfa.part2.Lambda.html#22641" class="InductiveConstructor Operator">⟩</a>
    <a id="26399" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3981" class="InductiveConstructor Operator">case</a> <a id="26404" href="plfa.part2.Lambda.html#4482" class="Function">two</a> <a id="26408" href="plfa.part2.Lambda.html#3981" class="InductiveConstructor Operator">[zero⇒</a> <a id="26415" href="plfa.part2.Lambda.html#4482" class="Function">two</a> <a id="26419" href="plfa.part2.Lambda.html#3981" class="InductiveConstructor Operator">|suc</a> <a id="26424" class="String">&quot;m&quot;</a> <a id="26428" href="plfa.part2.Lambda.html#3981" class="InductiveConstructor Operator">⇒</a> <a id="26430" href="plfa.part2.Lambda.html#3940" class="InductiveConstructor Operator">`suc</a> <a id="26435" class="Symbol">(</a><a id="26436" href="plfa.part2.Lambda.html#4516" class="Function">plus</a> <a id="26441" href="plfa.part2.Lambda.html#3858" class="InductiveConstructor Operator">·</a> <a id="26443" href="plfa.part2.Lambda.html#3773" class="InductiveConstructor Operator">`</a> <a id="26445" class="String">&quot;m&quot;</a> <a id="26449" href="plfa.part2.Lambda.html#3858" class="InductiveConstructor Operator">·</a> <a id="26451" href="plfa.part2.Lambda.html#4482" class="Function">two</a><a id="26454" class="Symbol">)</a> <a id="26456" href="plfa.part2.Lambda.html#3981" class="InductiveConstructor Operator">]</a>
  <a id="26460" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#22641" class="InductiveConstructor Operator">—→⟨</a> <a id="26464" href="plfa.part2.Lambda.html#20270" class="InductiveConstructor">β-suc</a> <a id="26470" class="Symbol">(</a><a id="26471" href="plfa.part2.Lambda.html#11690" class="InductiveConstructor">V-suc</a> <a id="26477" href="plfa.part2.Lambda.html#11642" class="InductiveConstructor">V-zero</a><a id="26483" class="Symbol">)</a> <a id="26485" href="plfa.part2.Lambda.html#22641" class="InductiveConstructor Operator">⟩</a>
    <a id="26491" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3940" class="InductiveConstructor Operator">`suc</a> <a id="26496" class="Symbol">(</a><a id="26497" href="plfa.part2.Lambda.html#4516" class="Function">plus</a> <a id="26502" href="plfa.part2.Lambda.html#3858" class="InductiveConstructor Operator">·</a> <a id="26504" href="plfa.part2.Lambda.html#3940" class="InductiveConstructor Operator">`suc</a> <a id="26509" href="plfa.part2.Lambda.html#3906" class="InductiveConstructor">`zero</a> <a id="26515" href="plfa.part2.Lambda.html#3858" class="InductiveConstructor Operator">·</a> <a id="26517" href="plfa.part2.Lambda.html#4482" class="Function">two</a><a id="26520" class="Symbol">)</a>
  <a id="26524" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#22641" class="InductiveConstructor Operator">—→⟨</a> <a id="26528" href="plfa.part2.Lambda.html#19893" class="InductiveConstructor">ξ-suc</a> <a id="26534" class="Symbol">(</a><a id="26535" href="plfa.part2.Lambda.html#19611" class="InductiveConstructor">ξ-·₁</a> <a id="26540" class="Symbol">(</a><a id="26541" href="plfa.part2.Lambda.html#19611" class="InductiveConstructor">ξ-·₁</a> <a id="26546" href="plfa.part2.Lambda.html#20421" class="InductiveConstructor">β-μ</a><a id="26549" class="Symbol">))</a> <a id="26552" href="plfa.part2.Lambda.html#22641" class="InductiveConstructor Operator">⟩</a>
    <a id="26558" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3940" class="InductiveConstructor Operator">`suc</a> <a id="26563" class="Symbol">((</a><a id="26565" href="plfa.part2.Lambda.html#3812" class="InductiveConstructor Operator">ƛ</a> <a id="26567" class="String">&quot;m&quot;</a> <a id="26571" href="plfa.part2.Lambda.html#3812" class="InductiveConstructor Operator">⇒</a> <a id="26573" href="plfa.part2.Lambda.html#3812" class="InductiveConstructor Operator">ƛ</a> <a id="26575" class="String">&quot;n&quot;</a> <a id="26579" href="plfa.part2.Lambda.html#3812" class="InductiveConstructor Operator">⇒</a>
      <a id="26587" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3981" class="InductiveConstructor Operator">case</a> <a id="26592" href="plfa.part2.Lambda.html#3773" class="InductiveConstructor Operator">`</a> <a id="26594" class="String">&quot;m&quot;</a> <a id="26598" href="plfa.part2.Lambda.html#3981" class="InductiveConstructor Operator">[zero⇒</a> <a id="26605" href="plfa.part2.Lambda.html#3773" class="InductiveConstructor Operator">`</a> <a id="26607" class="String">&quot;n&quot;</a> <a id="26611" href="plfa.part2.Lambda.html#3981" class="InductiveConstructor Operator">|suc</a> <a id="26616" class="String">&quot;m&quot;</a> <a id="26620" href="plfa.part2.Lambda.html#3981" class="InductiveConstructor Operator">⇒</a> <a id="26622" href="plfa.part2.Lambda.html#3940" class="InductiveConstructor Operator">`suc</a> <a id="26627" class="Symbol">(</a><a id="26628" href="plfa.part2.Lambda.html#4516" class="Function">plus</a> <a id="26633" href="plfa.part2.Lambda.html#3858" class="InductiveConstructor Operator">·</a> <a id="26635" href="plfa.part2.Lambda.html#3773" class="InductiveConstructor Operator">`</a> <a id="26637" class="String">&quot;m&quot;</a> <a id="26641" href="plfa.part2.Lambda.html#3858" class="InductiveConstructor Operator">·</a> <a id="26643" href="plfa.part2.Lambda.html#3773" class="InductiveConstructor Operator">`</a> <a id="26645" class="String">&quot;n&quot;</a><a id="26648" class="Symbol">)</a> <a id="26650" href="plfa.part2.Lambda.html#3981" class="InductiveConstructor Operator">]</a><a id="26651" class="Symbol">)</a>
        <a id="26661" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3858" class="InductiveConstructor Operator">·</a> <a id="26663" href="plfa.part2.Lambda.html#3940" class="InductiveConstructor Operator">`suc</a> <a id="26668" href="plfa.part2.Lambda.html#3906" class="InductiveConstructor">`zero</a> <a id="26674" href="plfa.part2.Lambda.html#3858" class="InductiveConstructor Operator">·</a> <a id="26676" href="plfa.part2.Lambda.html#4482" class="Function">two</a><a id="26679" class="Symbol">)</a>
  <a id="26683" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#22641" class="InductiveConstructor Operator">—→⟨</a> <a id="26687" href="plfa.part2.Lambda.html#19893" class="InductiveConstructor">ξ-suc</a> <a id="26693" class="Symbol">(</a><a id="26694" href="plfa.part2.Lambda.html#19611" class="InductiveConstructor">ξ-·₁</a> <a id="26699" class="Symbol">(</a><a id="26700" href="plfa.part2.Lambda.html#19787" class="InductiveConstructor">β-ƛ</a> <a id="26704" class="Symbol">(</a><a id="26705" href="plfa.part2.Lambda.html#11690" class="InductiveConstructor">V-suc</a> <a id="26711" href="plfa.part2.Lambda.html#11642" class="InductiveConstructor">V-zero</a><a id="26717" class="Symbol">)))</a> <a id="26721" href="plfa.part2.Lambda.html#22641" class="InductiveConstructor Operator">⟩</a>
    <a id="26727" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3940" class="InductiveConstructor Operator">`suc</a> <a id="26732" class="Symbol">((</a><a id="26734" href="plfa.part2.Lambda.html#3812" class="InductiveConstructor Operator">ƛ</a> <a id="26736" class="String">&quot;n&quot;</a> <a id="26740" href="plfa.part2.Lambda.html#3812" class="InductiveConstructor Operator">⇒</a>
      <a id="26748" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3981" class="InductiveConstructor Operator">case</a> <a id="26753" href="plfa.part2.Lambda.html#3940" class="InductiveConstructor Operator">`suc</a> <a id="26758" href="plfa.part2.Lambda.html#3906" class="InductiveConstructor">`zero</a> <a id="26764" href="plfa.part2.Lambda.html#3981" class="InductiveConstructor Operator">[zero⇒</a> <a id="26771" href="plfa.part2.Lambda.html#3773" class="InductiveConstructor Operator">`</a> <a id="26773" class="String">&quot;n&quot;</a> <a id="26777" href="plfa.part2.Lambda.html#3981" class="InductiveConstructor Operator">|suc</a> <a id="26782" class="String">&quot;m&quot;</a> <a id="26786" href="plfa.part2.Lambda.html#3981" class="InductiveConstructor Operator">⇒</a> <a id="26788" href="plfa.part2.Lambda.html#3940" class="InductiveConstructor Operator">`suc</a> <a id="26793" class="Symbol">(</a><a id="26794" href="plfa.part2.Lambda.html#4516" class="Function">plus</a> <a id="26799" href="plfa.part2.Lambda.html#3858" class="InductiveConstructor Operator">·</a> <a id="26801" href="plfa.part2.Lambda.html#3773" class="InductiveConstructor Operator">`</a> <a id="26803" class="String">&quot;m&quot;</a> <a id="26807" href="plfa.part2.Lambda.html#3858" class="InductiveConstructor Operator">·</a> <a id="26809" href="plfa.part2.Lambda.html#3773" class="InductiveConstructor Operator">`</a> <a id="26811" class="String">&quot;n&quot;</a><a id="26814" class="Symbol">)</a> <a id="26816" href="plfa.part2.Lambda.html#3981" class="InductiveConstructor Operator">]</a><a id="26817" class="Symbol">)</a>
        <a id="26827" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3858" class="InductiveConstructor Operator">·</a> <a id="26829" href="plfa.part2.Lambda.html#4482" class="Function">two</a><a id="26832" class="Symbol">)</a>
  <a id="26836" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#22641" class="InductiveConstructor Operator">—→⟨</a> <a id="26840" href="plfa.part2.Lambda.html#19893" class="InductiveConstructor">ξ-suc</a> <a id="26846" class="Symbol">(</a><a id="26847" href="plfa.part2.Lambda.html#19787" class="InductiveConstructor">β-ƛ</a> <a id="26851" class="Symbol">(</a><a id="26852" href="plfa.part2.Lambda.html#11690" class="InductiveConstructor">V-suc</a> <a id="26858" class="Symbol">(</a><a id="26859" href="plfa.part2.Lambda.html#11690" class="InductiveConstructor">V-suc</a> <a id="26865" href="plfa.part2.Lambda.html#11642" class="InductiveConstructor">V-zero</a><a id="26871" class="Symbol">)))</a> <a id="26875" href="plfa.part2.Lambda.html#22641" class="InductiveConstructor Operator">⟩</a>
    <a id="26881" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3940" class="InductiveConstructor Operator">`suc</a> <a id="26886" class="Symbol">(</a><a id="26887" href="plfa.part2.Lambda.html#3981" class="InductiveConstructor Operator">case</a> <a id="26892" href="plfa.part2.Lambda.html#3940" class="InductiveConstructor Operator">`suc</a> <a id="26897" href="plfa.part2.Lambda.html#3906" class="InductiveConstructor">`zero</a> <a id="26903" href="plfa.part2.Lambda.html#3981" class="InductiveConstructor Operator">[zero⇒</a> <a id="26910" href="plfa.part2.Lambda.html#4482" class="Function">two</a> <a id="26914" href="plfa.part2.Lambda.html#3981" class="InductiveConstructor Operator">|suc</a> <a id="26919" class="String">&quot;m&quot;</a> <a id="26923" href="plfa.part2.Lambda.html#3981" class="InductiveConstructor Operator">⇒</a> <a id="26925" href="plfa.part2.Lambda.html#3940" class="InductiveConstructor Operator">`suc</a> <a id="26930" class="Symbol">(</a><a id="26931" href="plfa.part2.Lambda.html#4516" class="Function">plus</a> <a id="26936" href="plfa.part2.Lambda.html#3858" class="InductiveConstructor Operator">·</a> <a id="26938" href="plfa.part2.Lambda.html#3773" class="InductiveConstructor Operator">`</a> <a id="26940" class="String">&quot;m&quot;</a> <a id="26944" href="plfa.part2.Lambda.html#3858" class="InductiveConstructor Operator">·</a> <a id="26946" href="plfa.part2.Lambda.html#4482" class="Function">two</a><a id="26949" class="Symbol">)</a> <a id="26951" href="plfa.part2.Lambda.html#3981" class="InductiveConstructor Operator">]</a><a id="26952" class="Symbol">)</a>
  <a id="26956" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#22641" class="InductiveConstructor Operator">—→⟨</a> <a id="26960" href="plfa.part2.Lambda.html#19893" class="InductiveConstructor">ξ-suc</a> <a id="26966" class="Symbol">(</a><a id="26967" href="plfa.part2.Lambda.html#20270" class="InductiveConstructor">β-suc</a> <a id="26973" href="plfa.part2.Lambda.html#11642" class="InductiveConstructor">V-zero</a><a id="26979" class="Symbol">)</a> <a id="26981" href="plfa.part2.Lambda.html#22641" class="InductiveConstructor Operator">⟩</a>
    <a id="26987" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3940" class="InductiveConstructor Operator">`suc</a> <a id="26992" href="plfa.part2.Lambda.html#3940" class="InductiveConstructor Operator">`suc</a> <a id="26997" class="Symbol">(</a><a id="26998" href="plfa.part2.Lambda.html#4516" class="Function">plus</a> <a id="27003" href="plfa.part2.Lambda.html#3858" class="InductiveConstructor Operator">·</a> <a id="27005" href="plfa.part2.Lambda.html#3906" class="InductiveConstructor">`zero</a> <a id="27011" href="plfa.part2.Lambda.html#3858" class="InductiveConstructor Operator">·</a> <a id="27013" href="plfa.part2.Lambda.html#4482" class="Function">two</a><a id="27016" class="Symbol">)</a>
  <a id="27020" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#22641" class="InductiveConstructor Operator">—→⟨</a> <a id="27024" href="plfa.part2.Lambda.html#19893" class="InductiveConstructor">ξ-suc</a> <a id="27030" class="Symbol">(</a><a id="27031" href="plfa.part2.Lambda.html#19893" class="InductiveConstructor">ξ-suc</a> <a id="27037" class="Symbol">(</a><a id="27038" href="plfa.part2.Lambda.html#19611" class="InductiveConstructor">ξ-·₁</a> <a id="27043" class="Symbol">(</a><a id="27044" href="plfa.part2.Lambda.html#19611" class="InductiveConstructor">ξ-·₁</a> <a id="27049" href="plfa.part2.Lambda.html#20421" class="InductiveConstructor">β-μ</a><a id="27052" class="Symbol">)))</a> <a id="27056" href="plfa.part2.Lambda.html#22641" class="InductiveConstructor Operator">⟩</a>
    <a id="27062" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3940" class="InductiveConstructor Operator">`suc</a> <a id="27067" href="plfa.part2.Lambda.html#3940" class="InductiveConstructor Operator">`suc</a> <a id="27072" class="Symbol">((</a><a id="27074" href="plfa.part2.Lambda.html#3812" class="InductiveConstructor Operator">ƛ</a> <a id="27076" class="String">&quot;m&quot;</a> <a id="27080" href="plfa.part2.Lambda.html#3812" class="InductiveConstructor Operator">⇒</a> <a id="27082" href="plfa.part2.Lambda.html#3812" class="InductiveConstructor Operator">ƛ</a> <a id="27084" class="String">&quot;n&quot;</a> <a id="27088" href="plfa.part2.Lambda.html#3812" class="InductiveConstructor Operator">⇒</a>
      <a id="27096" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3981" class="InductiveConstructor Operator">case</a> <a id="27101" href="plfa.part2.Lambda.html#3773" class="InductiveConstructor Operator">`</a> <a id="27103" class="String">&quot;m&quot;</a> <a id="27107" href="plfa.part2.Lambda.html#3981" class="InductiveConstructor Operator">[zero⇒</a> <a id="27114" href="plfa.part2.Lambda.html#3773" class="InductiveConstructor Operator">`</a> <a id="27116" class="String">&quot;n&quot;</a> <a id="27120" href="plfa.part2.Lambda.html#3981" class="InductiveConstructor Operator">|suc</a> <a id="27125" class="String">&quot;m&quot;</a> <a id="27129" href="plfa.part2.Lambda.html#3981" class="InductiveConstructor Operator">⇒</a> <a id="27131" href="plfa.part2.Lambda.html#3940" class="InductiveConstructor Operator">`suc</a> <a id="27136" class="Symbol">(</a><a id="27137" href="plfa.part2.Lambda.html#4516" class="Function">plus</a> <a id="27142" href="plfa.part2.Lambda.html#3858" class="InductiveConstructor Operator">·</a> <a id="27144" href="plfa.part2.Lambda.html#3773" class="InductiveConstructor Operator">`</a> <a id="27146" class="String">&quot;m&quot;</a> <a id="27150" href="plfa.part2.Lambda.html#3858" class="InductiveConstructor Operator">·</a> <a id="27152" href="plfa.part2.Lambda.html#3773" class="InductiveConstructor Operator">`</a> <a id="27154" class="String">&quot;n&quot;</a><a id="27157" class="Symbol">)</a> <a id="27159" href="plfa.part2.Lambda.html#3981" class="InductiveConstructor Operator">]</a><a id="27160" class="Symbol">)</a>
        <a id="27170" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3858" class="InductiveConstructor Operator">·</a> <a id="27172" href="plfa.part2.Lambda.html#3906" class="InductiveConstructor">`zero</a> <a id="27178" href="plfa.part2.Lambda.html#3858" class="InductiveConstructor Operator">·</a> <a id="27180" href="plfa.part2.Lambda.html#4482" class="Function">two</a><a id="27183" class="Symbol">)</a>
  <a id="27187" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#22641" class="InductiveConstructor Operator">—→⟨</a> <a id="27191" href="plfa.part2.Lambda.html#19893" class="InductiveConstructor">ξ-suc</a> <a id="27197" class="Symbol">(</a><a id="27198" href="plfa.part2.Lambda.html#19893" class="InductiveConstructor">ξ-suc</a> <a id="27204" class="Symbol">(</a><a id="27205" href="plfa.part2.Lambda.html#19611" class="InductiveConstructor">ξ-·₁</a> <a id="27210" class="Symbol">(</a><a id="27211" href="plfa.part2.Lambda.html#19787" class="InductiveConstructor">β-ƛ</a> <a id="27215" href="plfa.part2.Lambda.html#11642" class="InductiveConstructor">V-zero</a><a id="27221" class="Symbol">)))</a> <a id="27225" href="plfa.part2.Lambda.html#22641" class="InductiveConstructor Operator">⟩</a>
    <a id="27231" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3940" class="InductiveConstructor Operator">`suc</a> <a id="27236" href="plfa.part2.Lambda.html#3940" class="InductiveConstructor Operator">`suc</a> <a id="27241" class="Symbol">((</a><a id="27243" href="plfa.part2.Lambda.html#3812" class="InductiveConstructor Operator">ƛ</a> <a id="27245" class="String">&quot;n&quot;</a> <a id="27249" href="plfa.part2.Lambda.html#3812" class="InductiveConstructor Operator">⇒</a>
      <a id="27257" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3981" class="InductiveConstructor Operator">case</a> <a id="27262" href="plfa.part2.Lambda.html#3906" class="InductiveConstructor">`zero</a> <a id="27268" href="plfa.part2.Lambda.html#3981" class="InductiveConstructor Operator">[zero⇒</a> <a id="27275" href="plfa.part2.Lambda.html#3773" class="InductiveConstructor Operator">`</a> <a id="27277" class="String">&quot;n&quot;</a> <a id="27281" href="plfa.part2.Lambda.html#3981" class="InductiveConstructor Operator">|suc</a> <a id="27286" class="String">&quot;m&quot;</a> <a id="27290" href="plfa.part2.Lambda.html#3981" class="InductiveConstructor Operator">⇒</a> <a id="27292" href="plfa.part2.Lambda.html#3940" class="InductiveConstructor Operator">`suc</a> <a id="27297" class="Symbol">(</a><a id="27298" href="plfa.part2.Lambda.html#4516" class="Function">plus</a> <a id="27303" href="plfa.part2.Lambda.html#3858" class="InductiveConstructor Operator">·</a> <a id="27305" href="plfa.part2.Lambda.html#3773" class="InductiveConstructor Operator">`</a> <a id="27307" class="String">&quot;m&quot;</a> <a id="27311" href="plfa.part2.Lambda.html#3858" class="InductiveConstructor Operator">·</a> <a id="27313" href="plfa.part2.Lambda.html#3773" class="InductiveConstructor Operator">`</a> <a id="27315" class="String">&quot;n&quot;</a><a id="27318" class="Symbol">)</a> <a id="27320" href="plfa.part2.Lambda.html#3981" class="InductiveConstructor Operator">]</a><a id="27321" class="Symbol">)</a>
        <a id="27331" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3858" class="InductiveConstructor Operator">·</a> <a id="27333" href="plfa.part2.Lambda.html#4482" class="Function">two</a><a id="27336" class="Symbol">)</a>
  <a id="27340" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#22641" class="InductiveConstructor Operator">—→⟨</a> <a id="27344" href="plfa.part2.Lambda.html#19893" class="InductiveConstructor">ξ-suc</a> <a id="27350" class="Symbol">(</a><a id="27351" href="plfa.part2.Lambda.html#19893" class="InductiveConstructor">ξ-suc</a> <a id="27357" class="Symbol">(</a><a id="27358" href="plfa.part2.Lambda.html#19787" class="InductiveConstructor">β-ƛ</a> <a id="27362" class="Symbol">(</a><a id="27363" href="plfa.part2.Lambda.html#11690" class="InductiveConstructor">V-suc</a> <a id="27369" class="Symbol">(</a><a id="27370" href="plfa.part2.Lambda.html#11690" class="InductiveConstructor">V-suc</a> <a id="27376" href="plfa.part2.Lambda.html#11642" class="InductiveConstructor">V-zero</a><a id="27382" class="Symbol">))))</a> <a id="27387" href="plfa.part2.Lambda.html#22641" class="InductiveConstructor Operator">⟩</a>
    <a id="27393" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3940" class="InductiveConstructor Operator">`suc</a> <a id="27398" href="plfa.part2.Lambda.html#3940" class="InductiveConstructor Operator">`suc</a> <a id="27403" class="Symbol">(</a><a id="27404" href="plfa.part2.Lambda.html#3981" class="InductiveConstructor Operator">case</a> <a id="27409" href="plfa.part2.Lambda.html#3906" class="InductiveConstructor">`zero</a> <a id="27415" href="plfa.part2.Lambda.html#3981" class="InductiveConstructor Operator">[zero⇒</a> <a id="27422" href="plfa.part2.Lambda.html#4482" class="Function">two</a> <a id="27426" href="plfa.part2.Lambda.html#3981" class="InductiveConstructor Operator">|suc</a> <a id="27431" class="String">&quot;m&quot;</a> <a id="27435" href="plfa.part2.Lambda.html#3981" class="InductiveConstructor Operator">⇒</a> <a id="27437" href="plfa.part2.Lambda.html#3940" class="InductiveConstructor Operator">`suc</a> <a id="27442" class="Symbol">(</a><a id="27443" href="plfa.part2.Lambda.html#4516" class="Function">plus</a> <a id="27448" href="plfa.part2.Lambda.html#3858" class="InductiveConstructor Operator">·</a> <a id="27450" href="plfa.part2.Lambda.html#3773" class="InductiveConstructor Operator">`</a> <a id="27452" class="String">&quot;m&quot;</a> <a id="27456" href="plfa.part2.Lambda.html#3858" class="InductiveConstructor Operator">·</a> <a id="27458" href="plfa.part2.Lambda.html#4482" class="Function">two</a><a id="27461" class="Symbol">)</a> <a id="27463" href="plfa.part2.Lambda.html#3981" class="InductiveConstructor Operator">]</a><a id="27464" class="Symbol">)</a>
  <a id="27468" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#22641" class="InductiveConstructor Operator">—→⟨</a> <a id="27472" href="plfa.part2.Lambda.html#19893" class="InductiveConstructor">ξ-suc</a> <a id="27478" class="Symbol">(</a><a id="27479" href="plfa.part2.Lambda.html#19893" class="InductiveConstructor">ξ-suc</a> <a id="27485" href="plfa.part2.Lambda.html#20157" class="InductiveConstructor">β-zero</a><a id="27491" class="Symbol">)</a> <a id="27493" href="plfa.part2.Lambda.html#22641" class="InductiveConstructor Operator">⟩</a>
    <a id="27499" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3940" class="InductiveConstructor Operator">`suc</a> <a id="27504" class="Symbol">(</a><a id="27505" href="plfa.part2.Lambda.html#3940" class="InductiveConstructor Operator">`suc</a> <a id="27510" class="Symbol">(</a><a id="27511" href="plfa.part2.Lambda.html#3940" class="InductiveConstructor Operator">`suc</a> <a id="27516" class="Symbol">(</a><a id="27517" href="plfa.part2.Lambda.html#3940" class="InductiveConstructor Operator">`suc</a> <a id="27522" href="plfa.part2.Lambda.html#3906" class="InductiveConstructor">`zero</a><a id="27527" class="Symbol">)))</a>
  <a id="27533" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#22600" class="InductiveConstructor Operator">∎</a>
</pre>{% endraw %}
And here is a similar sample reduction for Church numerals:
{% raw %}<pre class="Agda"><a id="27604" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#27604" class="Function">_</a> <a id="27606" class="Symbol">:</a> <a id="27608" href="plfa.part2.Lambda.html#5792" class="Function">plusᶜ</a> <a id="27614" href="plfa.part2.Lambda.html#3858" class="InductiveConstructor Operator">·</a> <a id="27616" href="plfa.part2.Lambda.html#5731" class="Function">twoᶜ</a> <a id="27621" href="plfa.part2.Lambda.html#3858" class="InductiveConstructor Operator">·</a> <a id="27623" href="plfa.part2.Lambda.html#5731" class="Function">twoᶜ</a> <a id="27628" href="plfa.part2.Lambda.html#3858" class="InductiveConstructor Operator">·</a> <a id="27630" href="plfa.part2.Lambda.html#5896" class="Function">sucᶜ</a> <a id="27635" href="plfa.part2.Lambda.html#3858" class="InductiveConstructor Operator">·</a> <a id="27637" href="plfa.part2.Lambda.html#3906" class="InductiveConstructor">`zero</a> <a id="27643" href="plfa.part2.Lambda.html#22567" class="Datatype Operator">—↠</a> <a id="27646" href="plfa.part2.Lambda.html#3940" class="InductiveConstructor Operator">`suc</a> <a id="27651" href="plfa.part2.Lambda.html#3940" class="InductiveConstructor Operator">`suc</a> <a id="27656" href="plfa.part2.Lambda.html#3940" class="InductiveConstructor Operator">`suc</a> <a id="27661" href="plfa.part2.Lambda.html#3940" class="InductiveConstructor Operator">`suc</a> <a id="27666" href="plfa.part2.Lambda.html#3906" class="InductiveConstructor">`zero</a>
<a id="27672" class="Symbol">_</a> <a id="27674" class="Symbol">=</a>
  <a id="27678" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#22717" class="Function Operator">begin</a>
    <a id="27688" class="Symbol">(</a><a id="27689" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3812" class="InductiveConstructor Operator">ƛ</a> <a id="27691" class="String">&quot;m&quot;</a> <a id="27695" href="plfa.part2.Lambda.html#3812" class="InductiveConstructor Operator">⇒</a> <a id="27697" href="plfa.part2.Lambda.html#3812" class="InductiveConstructor Operator">ƛ</a> <a id="27699" class="String">&quot;n&quot;</a> <a id="27703" href="plfa.part2.Lambda.html#3812" class="InductiveConstructor Operator">⇒</a> <a id="27705" href="plfa.part2.Lambda.html#3812" class="InductiveConstructor Operator">ƛ</a> <a id="27707" class="String">&quot;s&quot;</a> <a id="27711" href="plfa.part2.Lambda.html#3812" class="InductiveConstructor Operator">⇒</a> <a id="27713" href="plfa.part2.Lambda.html#3812" class="InductiveConstructor Operator">ƛ</a> <a id="27715" class="String">&quot;z&quot;</a> <a id="27719" href="plfa.part2.Lambda.html#3812" class="InductiveConstructor Operator">⇒</a> <a id="27721" href="plfa.part2.Lambda.html#3773" class="InductiveConstructor Operator">`</a> <a id="27723" class="String">&quot;m&quot;</a> <a id="27727" href="plfa.part2.Lambda.html#3858" class="InductiveConstructor Operator">·</a> <a id="27729" href="plfa.part2.Lambda.html#3773" class="InductiveConstructor Operator">`</a> <a id="27731" class="String">&quot;s&quot;</a> <a id="27735" href="plfa.part2.Lambda.html#3858" class="InductiveConstructor Operator">·</a> <a id="27737" class="Symbol">(</a><a id="27738" href="plfa.part2.Lambda.html#3773" class="InductiveConstructor Operator">`</a> <a id="27740" class="String">&quot;n&quot;</a> <a id="27744" href="plfa.part2.Lambda.html#3858" class="InductiveConstructor Operator">·</a> <a id="27746" href="plfa.part2.Lambda.html#3773" class="InductiveConstructor Operator">`</a> <a id="27748" class="String">&quot;s&quot;</a> <a id="27752" href="plfa.part2.Lambda.html#3858" class="InductiveConstructor Operator">·</a> <a id="27754" href="plfa.part2.Lambda.html#3773" class="InductiveConstructor Operator">`</a> <a id="27756" class="String">&quot;z&quot;</a><a id="27759" class="Symbol">))</a>
      <a id="27768" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3858" class="InductiveConstructor Operator">·</a> <a id="27770" href="plfa.part2.Lambda.html#5731" class="Function">twoᶜ</a> <a id="27775" href="plfa.part2.Lambda.html#3858" class="InductiveConstructor Operator">·</a> <a id="27777" href="plfa.part2.Lambda.html#5731" class="Function">twoᶜ</a> <a id="27782" href="plfa.part2.Lambda.html#3858" class="InductiveConstructor Operator">·</a> <a id="27784" href="plfa.part2.Lambda.html#5896" class="Function">sucᶜ</a> <a id="27789" href="plfa.part2.Lambda.html#3858" class="InductiveConstructor Operator">·</a> <a id="27791" href="plfa.part2.Lambda.html#3906" class="InductiveConstructor">`zero</a>
  <a id="27799" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#22641" class="InductiveConstructor Operator">—→⟨</a> <a id="27803" href="plfa.part2.Lambda.html#19611" class="InductiveConstructor">ξ-·₁</a> <a id="27808" class="Symbol">(</a><a id="27809" href="plfa.part2.Lambda.html#19611" class="InductiveConstructor">ξ-·₁</a> <a id="27814" class="Symbol">(</a><a id="27815" href="plfa.part2.Lambda.html#19611" class="InductiveConstructor">ξ-·₁</a> <a id="27820" class="Symbol">(</a><a id="27821" href="plfa.part2.Lambda.html#19787" class="InductiveConstructor">β-ƛ</a> <a id="27825" href="plfa.part2.Lambda.html#11581" class="InductiveConstructor">V-ƛ</a><a id="27828" class="Symbol">)))</a> <a id="27832" href="plfa.part2.Lambda.html#22641" class="InductiveConstructor Operator">⟩</a>
    <a id="27838" class="Symbol">(</a><a id="27839" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3812" class="InductiveConstructor Operator">ƛ</a> <a id="27841" class="String">&quot;n&quot;</a> <a id="27845" href="plfa.part2.Lambda.html#3812" class="InductiveConstructor Operator">⇒</a> <a id="27847" href="plfa.part2.Lambda.html#3812" class="InductiveConstructor Operator">ƛ</a> <a id="27849" class="String">&quot;s&quot;</a> <a id="27853" href="plfa.part2.Lambda.html#3812" class="InductiveConstructor Operator">⇒</a> <a id="27855" href="plfa.part2.Lambda.html#3812" class="InductiveConstructor Operator">ƛ</a> <a id="27857" class="String">&quot;z&quot;</a> <a id="27861" href="plfa.part2.Lambda.html#3812" class="InductiveConstructor Operator">⇒</a> <a id="27863" href="plfa.part2.Lambda.html#5731" class="Function">twoᶜ</a> <a id="27868" href="plfa.part2.Lambda.html#3858" class="InductiveConstructor Operator">·</a> <a id="27870" href="plfa.part2.Lambda.html#3773" class="InductiveConstructor Operator">`</a> <a id="27872" class="String">&quot;s&quot;</a> <a id="27876" href="plfa.part2.Lambda.html#3858" class="InductiveConstructor Operator">·</a> <a id="27878" class="Symbol">(</a><a id="27879" href="plfa.part2.Lambda.html#3773" class="InductiveConstructor Operator">`</a> <a id="27881" class="String">&quot;n&quot;</a> <a id="27885" href="plfa.part2.Lambda.html#3858" class="InductiveConstructor Operator">·</a> <a id="27887" href="plfa.part2.Lambda.html#3773" class="InductiveConstructor Operator">`</a> <a id="27889" class="String">&quot;s&quot;</a> <a id="27893" href="plfa.part2.Lambda.html#3858" class="InductiveConstructor Operator">·</a> <a id="27895" href="plfa.part2.Lambda.html#3773" class="InductiveConstructor Operator">`</a> <a id="27897" class="String">&quot;z&quot;</a><a id="27900" class="Symbol">))</a>
      <a id="27909" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3858" class="InductiveConstructor Operator">·</a> <a id="27911" href="plfa.part2.Lambda.html#5731" class="Function">twoᶜ</a> <a id="27916" href="plfa.part2.Lambda.html#3858" class="InductiveConstructor Operator">·</a> <a id="27918" href="plfa.part2.Lambda.html#5896" class="Function">sucᶜ</a> <a id="27923" href="plfa.part2.Lambda.html#3858" class="InductiveConstructor Operator">·</a> <a id="27925" href="plfa.part2.Lambda.html#3906" class="InductiveConstructor">`zero</a>
  <a id="27933" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#22641" class="InductiveConstructor Operator">—→⟨</a> <a id="27937" href="plfa.part2.Lambda.html#19611" class="InductiveConstructor">ξ-·₁</a> <a id="27942" class="Symbol">(</a><a id="27943" href="plfa.part2.Lambda.html#19611" class="InductiveConstructor">ξ-·₁</a> <a id="27948" class="Symbol">(</a><a id="27949" href="plfa.part2.Lambda.html#19787" class="InductiveConstructor">β-ƛ</a> <a id="27953" href="plfa.part2.Lambda.html#11581" class="InductiveConstructor">V-ƛ</a><a id="27956" class="Symbol">))</a> <a id="27959" href="plfa.part2.Lambda.html#22641" class="InductiveConstructor Operator">⟩</a>
    <a id="27965" class="Symbol">(</a><a id="27966" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3812" class="InductiveConstructor Operator">ƛ</a> <a id="27968" class="String">&quot;s&quot;</a> <a id="27972" href="plfa.part2.Lambda.html#3812" class="InductiveConstructor Operator">⇒</a> <a id="27974" href="plfa.part2.Lambda.html#3812" class="InductiveConstructor Operator">ƛ</a> <a id="27976" class="String">&quot;z&quot;</a> <a id="27980" href="plfa.part2.Lambda.html#3812" class="InductiveConstructor Operator">⇒</a> <a id="27982" href="plfa.part2.Lambda.html#5731" class="Function">twoᶜ</a> <a id="27987" href="plfa.part2.Lambda.html#3858" class="InductiveConstructor Operator">·</a> <a id="27989" href="plfa.part2.Lambda.html#3773" class="InductiveConstructor Operator">`</a> <a id="27991" class="String">&quot;s&quot;</a> <a id="27995" href="plfa.part2.Lambda.html#3858" class="InductiveConstructor Operator">·</a> <a id="27997" class="Symbol">(</a><a id="27998" href="plfa.part2.Lambda.html#5731" class="Function">twoᶜ</a> <a id="28003" href="plfa.part2.Lambda.html#3858" class="InductiveConstructor Operator">·</a> <a id="28005" href="plfa.part2.Lambda.html#3773" class="InductiveConstructor Operator">`</a> <a id="28007" class="String">&quot;s&quot;</a> <a id="28011" href="plfa.part2.Lambda.html#3858" class="InductiveConstructor Operator">·</a> <a id="28013" href="plfa.part2.Lambda.html#3773" class="InductiveConstructor Operator">`</a> <a id="28015" class="String">&quot;z&quot;</a><a id="28018" class="Symbol">))</a> <a id="28021" href="plfa.part2.Lambda.html#3858" class="InductiveConstructor Operator">·</a> <a id="28023" href="plfa.part2.Lambda.html#5896" class="Function">sucᶜ</a> <a id="28028" href="plfa.part2.Lambda.html#3858" class="InductiveConstructor Operator">·</a> <a id="28030" href="plfa.part2.Lambda.html#3906" class="InductiveConstructor">`zero</a>
  <a id="28038" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#22641" class="InductiveConstructor Operator">—→⟨</a> <a id="28042" href="plfa.part2.Lambda.html#19611" class="InductiveConstructor">ξ-·₁</a> <a id="28047" class="Symbol">(</a><a id="28048" href="plfa.part2.Lambda.html#19787" class="InductiveConstructor">β-ƛ</a> <a id="28052" href="plfa.part2.Lambda.html#11581" class="InductiveConstructor">V-ƛ</a><a id="28055" class="Symbol">)</a> <a id="28057" href="plfa.part2.Lambda.html#22641" class="InductiveConstructor Operator">⟩</a>
    <a id="28063" class="Symbol">(</a><a id="28064" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3812" class="InductiveConstructor Operator">ƛ</a> <a id="28066" class="String">&quot;z&quot;</a> <a id="28070" href="plfa.part2.Lambda.html#3812" class="InductiveConstructor Operator">⇒</a> <a id="28072" href="plfa.part2.Lambda.html#5731" class="Function">twoᶜ</a> <a id="28077" href="plfa.part2.Lambda.html#3858" class="InductiveConstructor Operator">·</a> <a id="28079" href="plfa.part2.Lambda.html#5896" class="Function">sucᶜ</a> <a id="28084" href="plfa.part2.Lambda.html#3858" class="InductiveConstructor Operator">·</a> <a id="28086" class="Symbol">(</a><a id="28087" href="plfa.part2.Lambda.html#5731" class="Function">twoᶜ</a> <a id="28092" href="plfa.part2.Lambda.html#3858" class="InductiveConstructor Operator">·</a> <a id="28094" href="plfa.part2.Lambda.html#5896" class="Function">sucᶜ</a> <a id="28099" href="plfa.part2.Lambda.html#3858" class="InductiveConstructor Operator">·</a> <a id="28101" href="plfa.part2.Lambda.html#3773" class="InductiveConstructor Operator">`</a> <a id="28103" class="String">&quot;z&quot;</a><a id="28106" class="Symbol">))</a> <a id="28109" href="plfa.part2.Lambda.html#3858" class="InductiveConstructor Operator">·</a> <a id="28111" href="plfa.part2.Lambda.html#3906" class="InductiveConstructor">`zero</a>
  <a id="28119" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#22641" class="InductiveConstructor Operator">—→⟨</a> <a id="28123" href="plfa.part2.Lambda.html#19787" class="InductiveConstructor">β-ƛ</a> <a id="28127" href="plfa.part2.Lambda.html#11642" class="InductiveConstructor">V-zero</a> <a id="28134" href="plfa.part2.Lambda.html#22641" class="InductiveConstructor Operator">⟩</a>
    <a id="28140" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#5731" class="Function">twoᶜ</a> <a id="28145" href="plfa.part2.Lambda.html#3858" class="InductiveConstructor Operator">·</a> <a id="28147" href="plfa.part2.Lambda.html#5896" class="Function">sucᶜ</a> <a id="28152" href="plfa.part2.Lambda.html#3858" class="InductiveConstructor Operator">·</a> <a id="28154" class="Symbol">(</a><a id="28155" href="plfa.part2.Lambda.html#5731" class="Function">twoᶜ</a> <a id="28160" href="plfa.part2.Lambda.html#3858" class="InductiveConstructor Operator">·</a> <a id="28162" href="plfa.part2.Lambda.html#5896" class="Function">sucᶜ</a> <a id="28167" href="plfa.part2.Lambda.html#3858" class="InductiveConstructor Operator">·</a> <a id="28169" href="plfa.part2.Lambda.html#3906" class="InductiveConstructor">`zero</a><a id="28174" class="Symbol">)</a>
  <a id="28178" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#22641" class="InductiveConstructor Operator">—→⟨</a> <a id="28182" href="plfa.part2.Lambda.html#19611" class="InductiveConstructor">ξ-·₁</a> <a id="28187" class="Symbol">(</a><a id="28188" href="plfa.part2.Lambda.html#19787" class="InductiveConstructor">β-ƛ</a> <a id="28192" href="plfa.part2.Lambda.html#11581" class="InductiveConstructor">V-ƛ</a><a id="28195" class="Symbol">)</a> <a id="28197" href="plfa.part2.Lambda.html#22641" class="InductiveConstructor Operator">⟩</a>
    <a id="28203" class="Symbol">(</a><a id="28204" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3812" class="InductiveConstructor Operator">ƛ</a> <a id="28206" class="String">&quot;z&quot;</a> <a id="28210" href="plfa.part2.Lambda.html#3812" class="InductiveConstructor Operator">⇒</a> <a id="28212" href="plfa.part2.Lambda.html#5896" class="Function">sucᶜ</a> <a id="28217" href="plfa.part2.Lambda.html#3858" class="InductiveConstructor Operator">·</a> <a id="28219" class="Symbol">(</a><a id="28220" href="plfa.part2.Lambda.html#5896" class="Function">sucᶜ</a> <a id="28225" href="plfa.part2.Lambda.html#3858" class="InductiveConstructor Operator">·</a> <a id="28227" href="plfa.part2.Lambda.html#3773" class="InductiveConstructor Operator">`</a> <a id="28229" class="String">&quot;z&quot;</a><a id="28232" class="Symbol">))</a> <a id="28235" href="plfa.part2.Lambda.html#3858" class="InductiveConstructor Operator">·</a> <a id="28237" class="Symbol">(</a><a id="28238" href="plfa.part2.Lambda.html#5731" class="Function">twoᶜ</a> <a id="28243" href="plfa.part2.Lambda.html#3858" class="InductiveConstructor Operator">·</a> <a id="28245" href="plfa.part2.Lambda.html#5896" class="Function">sucᶜ</a> <a id="28250" href="plfa.part2.Lambda.html#3858" class="InductiveConstructor Operator">·</a> <a id="28252" href="plfa.part2.Lambda.html#3906" class="InductiveConstructor">`zero</a><a id="28257" class="Symbol">)</a>
  <a id="28261" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#22641" class="InductiveConstructor Operator">—→⟨</a> <a id="28265" href="plfa.part2.Lambda.html#19692" class="InductiveConstructor">ξ-·₂</a> <a id="28270" href="plfa.part2.Lambda.html#11581" class="InductiveConstructor">V-ƛ</a> <a id="28274" class="Symbol">(</a><a id="28275" href="plfa.part2.Lambda.html#19611" class="InductiveConstructor">ξ-·₁</a> <a id="28280" class="Symbol">(</a><a id="28281" href="plfa.part2.Lambda.html#19787" class="InductiveConstructor">β-ƛ</a> <a id="28285" href="plfa.part2.Lambda.html#11581" class="InductiveConstructor">V-ƛ</a><a id="28288" class="Symbol">))</a> <a id="28291" href="plfa.part2.Lambda.html#22641" class="InductiveConstructor Operator">⟩</a>
    <a id="28297" class="Symbol">(</a><a id="28298" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3812" class="InductiveConstructor Operator">ƛ</a> <a id="28300" class="String">&quot;z&quot;</a> <a id="28304" href="plfa.part2.Lambda.html#3812" class="InductiveConstructor Operator">⇒</a> <a id="28306" href="plfa.part2.Lambda.html#5896" class="Function">sucᶜ</a> <a id="28311" href="plfa.part2.Lambda.html#3858" class="InductiveConstructor Operator">·</a> <a id="28313" class="Symbol">(</a><a id="28314" href="plfa.part2.Lambda.html#5896" class="Function">sucᶜ</a> <a id="28319" href="plfa.part2.Lambda.html#3858" class="InductiveConstructor Operator">·</a> <a id="28321" href="plfa.part2.Lambda.html#3773" class="InductiveConstructor Operator">`</a> <a id="28323" class="String">&quot;z&quot;</a><a id="28326" class="Symbol">))</a> <a id="28329" href="plfa.part2.Lambda.html#3858" class="InductiveConstructor Operator">·</a> <a id="28331" class="Symbol">((</a><a id="28333" href="plfa.part2.Lambda.html#3812" class="InductiveConstructor Operator">ƛ</a> <a id="28335" class="String">&quot;z&quot;</a> <a id="28339" href="plfa.part2.Lambda.html#3812" class="InductiveConstructor Operator">⇒</a> <a id="28341" href="plfa.part2.Lambda.html#5896" class="Function">sucᶜ</a> <a id="28346" href="plfa.part2.Lambda.html#3858" class="InductiveConstructor Operator">·</a> <a id="28348" class="Symbol">(</a><a id="28349" href="plfa.part2.Lambda.html#5896" class="Function">sucᶜ</a> <a id="28354" href="plfa.part2.Lambda.html#3858" class="InductiveConstructor Operator">·</a> <a id="28356" href="plfa.part2.Lambda.html#3773" class="InductiveConstructor Operator">`</a> <a id="28358" class="String">&quot;z&quot;</a><a id="28361" class="Symbol">))</a> <a id="28364" href="plfa.part2.Lambda.html#3858" class="InductiveConstructor Operator">·</a> <a id="28366" href="plfa.part2.Lambda.html#3906" class="InductiveConstructor">`zero</a><a id="28371" class="Symbol">)</a>
  <a id="28375" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#22641" class="InductiveConstructor Operator">—→⟨</a> <a id="28379" href="plfa.part2.Lambda.html#19692" class="InductiveConstructor">ξ-·₂</a> <a id="28384" href="plfa.part2.Lambda.html#11581" class="InductiveConstructor">V-ƛ</a> <a id="28388" class="Symbol">(</a><a id="28389" href="plfa.part2.Lambda.html#19787" class="InductiveConstructor">β-ƛ</a> <a id="28393" href="plfa.part2.Lambda.html#11642" class="InductiveConstructor">V-zero</a><a id="28399" class="Symbol">)</a> <a id="28401" href="plfa.part2.Lambda.html#22641" class="InductiveConstructor Operator">⟩</a>
    <a id="28407" class="Symbol">(</a><a id="28408" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3812" class="InductiveConstructor Operator">ƛ</a> <a id="28410" class="String">&quot;z&quot;</a> <a id="28414" href="plfa.part2.Lambda.html#3812" class="InductiveConstructor Operator">⇒</a> <a id="28416" href="plfa.part2.Lambda.html#5896" class="Function">sucᶜ</a> <a id="28421" href="plfa.part2.Lambda.html#3858" class="InductiveConstructor Operator">·</a> <a id="28423" class="Symbol">(</a><a id="28424" href="plfa.part2.Lambda.html#5896" class="Function">sucᶜ</a> <a id="28429" href="plfa.part2.Lambda.html#3858" class="InductiveConstructor Operator">·</a> <a id="28431" href="plfa.part2.Lambda.html#3773" class="InductiveConstructor Operator">`</a> <a id="28433" class="String">&quot;z&quot;</a><a id="28436" class="Symbol">))</a> <a id="28439" href="plfa.part2.Lambda.html#3858" class="InductiveConstructor Operator">·</a> <a id="28441" class="Symbol">(</a><a id="28442" href="plfa.part2.Lambda.html#5896" class="Function">sucᶜ</a> <a id="28447" href="plfa.part2.Lambda.html#3858" class="InductiveConstructor Operator">·</a> <a id="28449" class="Symbol">(</a><a id="28450" href="plfa.part2.Lambda.html#5896" class="Function">sucᶜ</a> <a id="28455" href="plfa.part2.Lambda.html#3858" class="InductiveConstructor Operator">·</a> <a id="28457" href="plfa.part2.Lambda.html#3906" class="InductiveConstructor">`zero</a><a id="28462" class="Symbol">))</a>
  <a id="28467" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#22641" class="InductiveConstructor Operator">—→⟨</a> <a id="28471" href="plfa.part2.Lambda.html#19692" class="InductiveConstructor">ξ-·₂</a> <a id="28476" href="plfa.part2.Lambda.html#11581" class="InductiveConstructor">V-ƛ</a> <a id="28480" class="Symbol">(</a><a id="28481" href="plfa.part2.Lambda.html#19692" class="InductiveConstructor">ξ-·₂</a> <a id="28486" href="plfa.part2.Lambda.html#11581" class="InductiveConstructor">V-ƛ</a> <a id="28490" class="Symbol">(</a><a id="28491" href="plfa.part2.Lambda.html#19787" class="InductiveConstructor">β-ƛ</a> <a id="28495" href="plfa.part2.Lambda.html#11642" class="InductiveConstructor">V-zero</a><a id="28501" class="Symbol">))</a> <a id="28504" href="plfa.part2.Lambda.html#22641" class="InductiveConstructor Operator">⟩</a>
    <a id="28510" class="Symbol">(</a><a id="28511" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3812" class="InductiveConstructor Operator">ƛ</a> <a id="28513" class="String">&quot;z&quot;</a> <a id="28517" href="plfa.part2.Lambda.html#3812" class="InductiveConstructor Operator">⇒</a> <a id="28519" href="plfa.part2.Lambda.html#5896" class="Function">sucᶜ</a> <a id="28524" href="plfa.part2.Lambda.html#3858" class="InductiveConstructor Operator">·</a> <a id="28526" class="Symbol">(</a><a id="28527" href="plfa.part2.Lambda.html#5896" class="Function">sucᶜ</a> <a id="28532" href="plfa.part2.Lambda.html#3858" class="InductiveConstructor Operator">·</a> <a id="28534" href="plfa.part2.Lambda.html#3773" class="InductiveConstructor Operator">`</a> <a id="28536" class="String">&quot;z&quot;</a><a id="28539" class="Symbol">))</a> <a id="28542" href="plfa.part2.Lambda.html#3858" class="InductiveConstructor Operator">·</a> <a id="28544" class="Symbol">(</a><a id="28545" href="plfa.part2.Lambda.html#5896" class="Function">sucᶜ</a> <a id="28550" href="plfa.part2.Lambda.html#3858" class="InductiveConstructor Operator">·</a> <a id="28552" class="Symbol">(</a><a id="28553" href="plfa.part2.Lambda.html#3940" class="InductiveConstructor Operator">`suc</a> <a id="28558" href="plfa.part2.Lambda.html#3906" class="InductiveConstructor">`zero</a><a id="28563" class="Symbol">))</a>
  <a id="28568" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#22641" class="InductiveConstructor Operator">—→⟨</a> <a id="28572" href="plfa.part2.Lambda.html#19692" class="InductiveConstructor">ξ-·₂</a> <a id="28577" href="plfa.part2.Lambda.html#11581" class="InductiveConstructor">V-ƛ</a> <a id="28581" class="Symbol">(</a><a id="28582" href="plfa.part2.Lambda.html#19787" class="InductiveConstructor">β-ƛ</a> <a id="28586" class="Symbol">(</a><a id="28587" href="plfa.part2.Lambda.html#11690" class="InductiveConstructor">V-suc</a> <a id="28593" href="plfa.part2.Lambda.html#11642" class="InductiveConstructor">V-zero</a><a id="28599" class="Symbol">))</a> <a id="28602" href="plfa.part2.Lambda.html#22641" class="InductiveConstructor Operator">⟩</a>
    <a id="28608" class="Symbol">(</a><a id="28609" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3812" class="InductiveConstructor Operator">ƛ</a> <a id="28611" class="String">&quot;z&quot;</a> <a id="28615" href="plfa.part2.Lambda.html#3812" class="InductiveConstructor Operator">⇒</a> <a id="28617" href="plfa.part2.Lambda.html#5896" class="Function">sucᶜ</a> <a id="28622" href="plfa.part2.Lambda.html#3858" class="InductiveConstructor Operator">·</a> <a id="28624" class="Symbol">(</a><a id="28625" href="plfa.part2.Lambda.html#5896" class="Function">sucᶜ</a> <a id="28630" href="plfa.part2.Lambda.html#3858" class="InductiveConstructor Operator">·</a> <a id="28632" href="plfa.part2.Lambda.html#3773" class="InductiveConstructor Operator">`</a> <a id="28634" class="String">&quot;z&quot;</a><a id="28637" class="Symbol">))</a> <a id="28640" href="plfa.part2.Lambda.html#3858" class="InductiveConstructor Operator">·</a> <a id="28642" class="Symbol">(</a><a id="28643" href="plfa.part2.Lambda.html#3940" class="InductiveConstructor Operator">`suc</a> <a id="28648" href="plfa.part2.Lambda.html#3940" class="InductiveConstructor Operator">`suc</a> <a id="28653" href="plfa.part2.Lambda.html#3906" class="InductiveConstructor">`zero</a><a id="28658" class="Symbol">)</a>
  <a id="28662" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#22641" class="InductiveConstructor Operator">—→⟨</a> <a id="28666" href="plfa.part2.Lambda.html#19787" class="InductiveConstructor">β-ƛ</a> <a id="28670" class="Symbol">(</a><a id="28671" href="plfa.part2.Lambda.html#11690" class="InductiveConstructor">V-suc</a> <a id="28677" class="Symbol">(</a><a id="28678" href="plfa.part2.Lambda.html#11690" class="InductiveConstructor">V-suc</a> <a id="28684" href="plfa.part2.Lambda.html#11642" class="InductiveConstructor">V-zero</a><a id="28690" class="Symbol">))</a> <a id="28693" href="plfa.part2.Lambda.html#22641" class="InductiveConstructor Operator">⟩</a>
    <a id="28699" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#5896" class="Function">sucᶜ</a> <a id="28704" href="plfa.part2.Lambda.html#3858" class="InductiveConstructor Operator">·</a> <a id="28706" class="Symbol">(</a><a id="28707" href="plfa.part2.Lambda.html#5896" class="Function">sucᶜ</a> <a id="28712" href="plfa.part2.Lambda.html#3858" class="InductiveConstructor Operator">·</a> <a id="28714" href="plfa.part2.Lambda.html#3940" class="InductiveConstructor Operator">`suc</a> <a id="28719" href="plfa.part2.Lambda.html#3940" class="InductiveConstructor Operator">`suc</a> <a id="28724" href="plfa.part2.Lambda.html#3906" class="InductiveConstructor">`zero</a><a id="28729" class="Symbol">)</a>
  <a id="28733" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#22641" class="InductiveConstructor Operator">—→⟨</a> <a id="28737" href="plfa.part2.Lambda.html#19692" class="InductiveConstructor">ξ-·₂</a> <a id="28742" href="plfa.part2.Lambda.html#11581" class="InductiveConstructor">V-ƛ</a> <a id="28746" class="Symbol">(</a><a id="28747" href="plfa.part2.Lambda.html#19787" class="InductiveConstructor">β-ƛ</a> <a id="28751" class="Symbol">(</a><a id="28752" href="plfa.part2.Lambda.html#11690" class="InductiveConstructor">V-suc</a> <a id="28758" class="Symbol">(</a><a id="28759" href="plfa.part2.Lambda.html#11690" class="InductiveConstructor">V-suc</a> <a id="28765" href="plfa.part2.Lambda.html#11642" class="InductiveConstructor">V-zero</a><a id="28771" class="Symbol">)))</a> <a id="28775" href="plfa.part2.Lambda.html#22641" class="InductiveConstructor Operator">⟩</a>
    <a id="28781" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#5896" class="Function">sucᶜ</a> <a id="28786" href="plfa.part2.Lambda.html#3858" class="InductiveConstructor Operator">·</a> <a id="28788" class="Symbol">(</a><a id="28789" href="plfa.part2.Lambda.html#3940" class="InductiveConstructor Operator">`suc</a> <a id="28794" href="plfa.part2.Lambda.html#3940" class="InductiveConstructor Operator">`suc</a> <a id="28799" href="plfa.part2.Lambda.html#3940" class="InductiveConstructor Operator">`suc</a> <a id="28804" href="plfa.part2.Lambda.html#3906" class="InductiveConstructor">`zero</a><a id="28809" class="Symbol">)</a>
  <a id="28813" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#22641" class="InductiveConstructor Operator">—→⟨</a> <a id="28817" href="plfa.part2.Lambda.html#19787" class="InductiveConstructor">β-ƛ</a> <a id="28821" class="Symbol">(</a><a id="28822" href="plfa.part2.Lambda.html#11690" class="InductiveConstructor">V-suc</a> <a id="28828" class="Symbol">(</a><a id="28829" href="plfa.part2.Lambda.html#11690" class="InductiveConstructor">V-suc</a> <a id="28835" class="Symbol">(</a><a id="28836" href="plfa.part2.Lambda.html#11690" class="InductiveConstructor">V-suc</a> <a id="28842" href="plfa.part2.Lambda.html#11642" class="InductiveConstructor">V-zero</a><a id="28848" class="Symbol">)))</a> <a id="28852" href="plfa.part2.Lambda.html#22641" class="InductiveConstructor Operator">⟩</a>
   <a id="28857" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3940" class="InductiveConstructor Operator">`suc</a> <a id="28862" class="Symbol">(</a><a id="28863" href="plfa.part2.Lambda.html#3940" class="InductiveConstructor Operator">`suc</a> <a id="28868" class="Symbol">(</a><a id="28869" href="plfa.part2.Lambda.html#3940" class="InductiveConstructor Operator">`suc</a> <a id="28874" class="Symbol">(</a><a id="28875" href="plfa.part2.Lambda.html#3940" class="InductiveConstructor Operator">`suc</a> <a id="28880" href="plfa.part2.Lambda.html#3906" class="InductiveConstructor">`zero</a><a id="28885" class="Symbol">)))</a>
  <a id="28891" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#22600" class="InductiveConstructor Operator">∎</a>
</pre>{% endraw %}
In the next chapter, we will see how to compute such reduction sequences.


#### Exercise `plus-example` (practice)

Write out the reduction sequence demonstrating that one plus one is two.

{% raw %}<pre class="Agda"><a id="29093" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}

## Syntax of types

We have just two types:

  * Functions, `A ⇒ B`
  * Naturals, `` `ℕ ``

As before, to avoid overlap we use variants of the names used by Agda.

Here is the syntax of types in BNF:

    A, B, C  ::=  A ⇒ B | `ℕ

And here it is formalised in Agda:

{% raw %}<pre class="Agda"><a id="29393" class="Keyword">infixr</a> <a id="29400" class="Number">7</a> <a id="29402" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#29431" class="InductiveConstructor Operator">_⇒_</a>

<a id="29407" class="Keyword">data</a> <a id="Type"></a><a id="29412" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#29412" class="Datatype">Type</a> <a id="29417" class="Symbol">:</a> <a id="29419" class="PrimitiveType">Set</a> <a id="29423" class="Keyword">where</a>
  <a id="Type._⇒_"></a><a id="29431" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#29431" class="InductiveConstructor Operator">_⇒_</a> <a id="29435" class="Symbol">:</a> <a id="29437" href="plfa.part2.Lambda.html#29412" class="Datatype">Type</a> <a id="29442" class="Symbol">→</a> <a id="29444" href="plfa.part2.Lambda.html#29412" class="Datatype">Type</a> <a id="29449" class="Symbol">→</a> <a id="29451" href="plfa.part2.Lambda.html#29412" class="Datatype">Type</a>
  <a id="Type.`ℕ"></a><a id="29458" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#29458" class="InductiveConstructor">`ℕ</a> <a id="29461" class="Symbol">:</a> <a id="29463" href="plfa.part2.Lambda.html#29412" class="Datatype">Type</a>
</pre>{% endraw %}
### Precedence

As in Agda, functions of two or more arguments are represented via
currying. This is made more convenient by declaring `_⇒_` to
associate to the right and `_·_` to associate to the left.
Thus:

* ``(`ℕ ⇒ `ℕ) ⇒ `ℕ ⇒ `ℕ`` stands for ``((`ℕ ⇒ `ℕ) ⇒ (`ℕ ⇒ `ℕ))``.
* `plus · two · two` stands for `(plus · two) · two`.

### Quiz

* What is the type of the following term?

    `` ƛ "s" ⇒ ` "s" · (` "s"  · `zero) ``

  1. `` (`ℕ ⇒ `ℕ) ⇒ (`ℕ ⇒ `ℕ) ``
  2. `` (`ℕ ⇒ `ℕ) ⇒ `ℕ ``
  3. `` `ℕ ⇒ (`ℕ ⇒ `ℕ) ``
  4. `` `ℕ ⇒ `ℕ ⇒ `ℕ ``
  5. `` `ℕ ⇒ `ℕ ``
  6. `` `ℕ ``

  Give more than one answer if appropriate.

* What is the type of the following term?

    `` (ƛ "s" ⇒ ` "s" · (` "s"  · `zero)) · sucᶜ ``

  1. `` (`ℕ ⇒ `ℕ) ⇒ (`ℕ ⇒ `ℕ) ``
  2. `` (`ℕ ⇒ `ℕ) ⇒ `ℕ ``
  3. `` `ℕ ⇒ (`ℕ ⇒ `ℕ) ``
  4. `` `ℕ ⇒ `ℕ ⇒ `ℕ ``
  5. `` `ℕ ⇒ `ℕ ``
  6. `` `ℕ ``

  Give more than one answer if appropriate.


## Typing

### Contexts

While reduction considers only closed terms, typing must
consider terms with free variables.  To type a term,
we must first type its subterms, and in particular in the
body of an abstraction its bound variable may appear free.

A _context_ associates variables with types.  We let `Γ` and `Δ` range
over contexts.  We write `∅` for the empty context, and `Γ , x ⦂ A`
for the context that extends `Γ` by mapping variable `x` to type `A`.
For example,

* `` ∅ , "s" ⦂ `ℕ ⇒ `ℕ , "z" ⦂ `ℕ ``

is the context that associates variable `` "s" `` with type `` `ℕ ⇒ `ℕ ``,
and variable `` "z" `` with type `` `ℕ ``.

Contexts are formalised as follows:

{% raw %}<pre class="Agda"><a id="31048" class="Keyword">infixl</a> <a id="31055" class="Number">5</a>  <a id="31058" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#31110" class="InductiveConstructor Operator">_,_⦂_</a>

<a id="31065" class="Keyword">data</a> <a id="Context"></a><a id="31070" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#31070" class="Datatype">Context</a> <a id="31078" class="Symbol">:</a> <a id="31080" class="PrimitiveType">Set</a> <a id="31084" class="Keyword">where</a>
  <a id="Context.∅"></a><a id="31092" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#31092" class="InductiveConstructor">∅</a>     <a id="31098" class="Symbol">:</a> <a id="31100" href="plfa.part2.Lambda.html#31070" class="Datatype">Context</a>
  <a id="Context._,_⦂_"></a><a id="31110" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#31110" class="InductiveConstructor Operator">_,_⦂_</a> <a id="31116" class="Symbol">:</a> <a id="31118" href="plfa.part2.Lambda.html#31070" class="Datatype">Context</a> <a id="31126" class="Symbol">→</a> <a id="31128" href="plfa.part2.Lambda.html#3653" class="Function">Id</a> <a id="31131" class="Symbol">→</a> <a id="31133" href="plfa.part2.Lambda.html#29412" class="Datatype">Type</a> <a id="31138" class="Symbol">→</a> <a id="31140" href="plfa.part2.Lambda.html#31070" class="Datatype">Context</a>
</pre>{% endraw %}

#### Exercise `Context-≃` (practice)

Show that `Context` is isomorphic to `List (Id × Type)`.
For instance, the isomorphism relates the context

    ∅ , "s" ⦂ `ℕ ⇒ `ℕ , "z" ⦂ `ℕ

to the list

    [ ⟨ "z" , `ℕ ⟩ , ⟨ "s" , `ℕ ⇒ `ℕ ⟩ ]

{% raw %}<pre class="Agda"><a id="31393" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}
### Lookup judgment

We have two forms of _judgment_.  The first is written

    Γ ∋ x ⦂ A

and indicates in context `Γ` that variable `x` has type `A`.
It is called _lookup_.
For example,

* `` ∅ , "s" ⦂ `ℕ ⇒ `ℕ , "z" ⦂ `ℕ ∋ "z" ⦂ `ℕ ``
* `` ∅ , "s" ⦂ `ℕ ⇒ `ℕ , "z" ⦂ `ℕ ∋ "s" ⦂ `ℕ ⇒ `ℕ ``

give us the types associated with variables `` "z" `` and `` "s" ``,
respectively.  The symbol `∋` (pronounced "ni", for "in"
backwards) is chosen because checking that `Γ ∋ x ⦂ A` is analogous to
checking whether `x ⦂ A` appears in a list corresponding to `Γ`.

If two variables in a context have the same name, then lookup
should return the most recently bound variable, which _shadows_
the other variables.  For example,

* `` ∅ , "x" ⦂ `ℕ ⇒ `ℕ , "x" ⦂ `ℕ ∋ "x" ⦂ `ℕ ``.

Here `` "x" ⦂ `ℕ ⇒ `ℕ `` is shadowed by `` "x" ⦂ `ℕ ``.

Lookup is formalised as follows:
{% raw %}<pre class="Agda"><a id="32282" class="Keyword">infix</a>  <a id="32289" class="Number">4</a>  <a id="32292" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#32304" class="Datatype Operator">_∋_⦂_</a>

<a id="32299" class="Keyword">data</a> <a id="_∋_⦂_"></a><a id="32304" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#32304" class="Datatype Operator">_∋_⦂_</a> <a id="32310" class="Symbol">:</a> <a id="32312" href="plfa.part2.Lambda.html#31070" class="Datatype">Context</a> <a id="32320" class="Symbol">→</a> <a id="32322" href="plfa.part2.Lambda.html#3653" class="Function">Id</a> <a id="32325" class="Symbol">→</a> <a id="32327" href="plfa.part2.Lambda.html#29412" class="Datatype">Type</a> <a id="32332" class="Symbol">→</a> <a id="32334" class="PrimitiveType">Set</a> <a id="32338" class="Keyword">where</a>

  <a id="_∋_⦂_.Z"></a><a id="32347" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#32347" class="InductiveConstructor">Z</a> <a id="32349" class="Symbol">:</a> <a id="32351" class="Symbol">∀</a> <a id="32353" class="Symbol">{</a><a id="32354" href="plfa.part2.Lambda.html#32354" class="Bound">Γ</a> <a id="32356" href="plfa.part2.Lambda.html#32356" class="Bound">x</a> <a id="32358" href="plfa.part2.Lambda.html#32358" class="Bound">A</a><a id="32359" class="Symbol">}</a>
      <a id="32367" class="Comment">------------------</a>
    <a id="32390" class="Symbol">→</a> <a id="32392" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#32354" class="Bound">Γ</a> <a id="32394" href="plfa.part2.Lambda.html#31110" class="InductiveConstructor Operator">,</a> <a id="32396" href="plfa.part2.Lambda.html#32356" class="Bound">x</a> <a id="32398" href="plfa.part2.Lambda.html#31110" class="InductiveConstructor Operator">⦂</a> <a id="32400" href="plfa.part2.Lambda.html#32358" class="Bound">A</a> <a id="32402" href="plfa.part2.Lambda.html#32304" class="Datatype Operator">∋</a> <a id="32404" href="plfa.part2.Lambda.html#32356" class="Bound">x</a> <a id="32406" href="plfa.part2.Lambda.html#32304" class="Datatype Operator">⦂</a> <a id="32408" href="plfa.part2.Lambda.html#32358" class="Bound">A</a>

  <a id="_∋_⦂_.S"></a><a id="32413" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#32413" class="InductiveConstructor">S</a> <a id="32415" class="Symbol">:</a> <a id="32417" class="Symbol">∀</a> <a id="32419" class="Symbol">{</a><a id="32420" href="plfa.part2.Lambda.html#32420" class="Bound">Γ</a> <a id="32422" href="plfa.part2.Lambda.html#32422" class="Bound">x</a> <a id="32424" href="plfa.part2.Lambda.html#32424" class="Bound">y</a> <a id="32426" href="plfa.part2.Lambda.html#32426" class="Bound">A</a> <a id="32428" href="plfa.part2.Lambda.html#32428" class="Bound">B</a><a id="32429" class="Symbol">}</a>
    <a id="32435" class="Symbol">→</a> <a id="32437" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#32422" class="Bound">x</a> <a id="32439" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#799" class="Function Operator">≢</a> <a id="32441" href="plfa.part2.Lambda.html#32424" class="Bound">y</a>
    <a id="32447" class="Symbol">→</a> <a id="32449" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#32420" class="Bound">Γ</a> <a id="32451" href="plfa.part2.Lambda.html#32304" class="Datatype Operator">∋</a> <a id="32453" href="plfa.part2.Lambda.html#32422" class="Bound">x</a> <a id="32455" href="plfa.part2.Lambda.html#32304" class="Datatype Operator">⦂</a> <a id="32457" href="plfa.part2.Lambda.html#32426" class="Bound">A</a>
      <a id="32465" class="Comment">------------------</a>
    <a id="32488" class="Symbol">→</a> <a id="32490" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#32420" class="Bound">Γ</a> <a id="32492" href="plfa.part2.Lambda.html#31110" class="InductiveConstructor Operator">,</a> <a id="32494" href="plfa.part2.Lambda.html#32424" class="Bound">y</a> <a id="32496" href="plfa.part2.Lambda.html#31110" class="InductiveConstructor Operator">⦂</a> <a id="32498" href="plfa.part2.Lambda.html#32428" class="Bound">B</a> <a id="32500" href="plfa.part2.Lambda.html#32304" class="Datatype Operator">∋</a> <a id="32502" href="plfa.part2.Lambda.html#32422" class="Bound">x</a> <a id="32504" href="plfa.part2.Lambda.html#32304" class="Datatype Operator">⦂</a> <a id="32506" href="plfa.part2.Lambda.html#32426" class="Bound">A</a>
</pre>{% endraw %}
The constructors `Z` and `S` correspond roughly to the constructors
`here` and `there` for the element-of relation `_∈_` on lists.
Constructor `S` takes an additional parameter, which ensures that
when we look up a variable that it is not _shadowed_ by another
variable with the same name to its left in the list.

### Typing judgment

The second judgment is written

    Γ ⊢ M ⦂ A

and indicates in context `Γ` that term `M` has type `A`.
Context `Γ` provides types for all the free variables in `M`.
For example:

* `` ∅ , "s" ⦂ `ℕ ⇒ `ℕ , "z" ⦂ `ℕ ⊢ ` "z" ⦂ `ℕ ``
* `` ∅ , "s" ⦂ `ℕ ⇒ `ℕ , "z" ⦂ `ℕ ⊢ ` "s" ⦂ `ℕ ⇒ `ℕ ``
* `` ∅ , "s" ⦂ `ℕ ⇒ `ℕ , "z" ⦂ `ℕ ⊢ ` "s" · ` "z" ⦂  `ℕ ``
* `` ∅ , "s" ⦂ `ℕ ⇒ `ℕ , "z" ⦂ `ℕ ⊢ ` "s" · (` "s" · ` "z") ⦂  `ℕ ``
* `` ∅ , "s" ⦂ `ℕ ⇒ `ℕ ⊢ ƛ "z" ⇒ ` "s" · (` "s" · ` "z") ⦂  `ℕ ⇒ `ℕ ``
* `` ∅ ⊢ ƛ "s" ⇒ ƛ "z" ⇒ ` "s" · (` "s" · ` "z") ⦂  (`ℕ ⇒ `ℕ) ⇒ `ℕ ⇒ `ℕ ``

Typing is formalised as follows:
{% raw %}<pre class="Agda"><a id="33446" class="Keyword">infix</a>  <a id="33453" class="Number">4</a>  <a id="33456" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#33468" class="Datatype Operator">_⊢_⦂_</a>

<a id="33463" class="Keyword">data</a> <a id="_⊢_⦂_"></a><a id="33468" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#33468" class="Datatype Operator">_⊢_⦂_</a> <a id="33474" class="Symbol">:</a> <a id="33476" href="plfa.part2.Lambda.html#31070" class="Datatype">Context</a> <a id="33484" class="Symbol">→</a> <a id="33486" href="plfa.part2.Lambda.html#3754" class="Datatype">Term</a> <a id="33491" class="Symbol">→</a> <a id="33493" href="plfa.part2.Lambda.html#29412" class="Datatype">Type</a> <a id="33498" class="Symbol">→</a> <a id="33500" class="PrimitiveType">Set</a> <a id="33504" class="Keyword">where</a>

  <a id="33513" class="Comment">-- Axiom</a>
  <a id="_⊢_⦂_.⊢`"></a><a id="33524" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#33524" class="InductiveConstructor">⊢`</a> <a id="33527" class="Symbol">:</a> <a id="33529" class="Symbol">∀</a> <a id="33531" class="Symbol">{</a><a id="33532" href="plfa.part2.Lambda.html#33532" class="Bound">Γ</a> <a id="33534" href="plfa.part2.Lambda.html#33534" class="Bound">x</a> <a id="33536" href="plfa.part2.Lambda.html#33536" class="Bound">A</a><a id="33537" class="Symbol">}</a>
    <a id="33543" class="Symbol">→</a> <a id="33545" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#33532" class="Bound">Γ</a> <a id="33547" href="plfa.part2.Lambda.html#32304" class="Datatype Operator">∋</a> <a id="33549" href="plfa.part2.Lambda.html#33534" class="Bound">x</a> <a id="33551" href="plfa.part2.Lambda.html#32304" class="Datatype Operator">⦂</a> <a id="33553" href="plfa.part2.Lambda.html#33536" class="Bound">A</a>
      <a id="33561" class="Comment">-----------</a>
    <a id="33577" class="Symbol">→</a> <a id="33579" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#33532" class="Bound">Γ</a> <a id="33581" href="plfa.part2.Lambda.html#33468" class="Datatype Operator">⊢</a> <a id="33583" href="plfa.part2.Lambda.html#3773" class="InductiveConstructor Operator">`</a> <a id="33585" href="plfa.part2.Lambda.html#33534" class="Bound">x</a> <a id="33587" href="plfa.part2.Lambda.html#33468" class="Datatype Operator">⦂</a> <a id="33589" href="plfa.part2.Lambda.html#33536" class="Bound">A</a>

  <a id="33594" class="Comment">-- ⇒-I</a>
  <a id="_⊢_⦂_.⊢ƛ"></a><a id="33603" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#33603" class="InductiveConstructor">⊢ƛ</a> <a id="33606" class="Symbol">:</a> <a id="33608" class="Symbol">∀</a> <a id="33610" class="Symbol">{</a><a id="33611" href="plfa.part2.Lambda.html#33611" class="Bound">Γ</a> <a id="33613" href="plfa.part2.Lambda.html#33613" class="Bound">x</a> <a id="33615" href="plfa.part2.Lambda.html#33615" class="Bound">N</a> <a id="33617" href="plfa.part2.Lambda.html#33617" class="Bound">A</a> <a id="33619" href="plfa.part2.Lambda.html#33619" class="Bound">B</a><a id="33620" class="Symbol">}</a>
    <a id="33626" class="Symbol">→</a> <a id="33628" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#33611" class="Bound">Γ</a> <a id="33630" href="plfa.part2.Lambda.html#31110" class="InductiveConstructor Operator">,</a> <a id="33632" href="plfa.part2.Lambda.html#33613" class="Bound">x</a> <a id="33634" href="plfa.part2.Lambda.html#31110" class="InductiveConstructor Operator">⦂</a> <a id="33636" href="plfa.part2.Lambda.html#33617" class="Bound">A</a> <a id="33638" href="plfa.part2.Lambda.html#33468" class="Datatype Operator">⊢</a> <a id="33640" href="plfa.part2.Lambda.html#33615" class="Bound">N</a> <a id="33642" href="plfa.part2.Lambda.html#33468" class="Datatype Operator">⦂</a> <a id="33644" href="plfa.part2.Lambda.html#33619" class="Bound">B</a>
      <a id="33652" class="Comment">-------------------</a>
    <a id="33676" class="Symbol">→</a> <a id="33678" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#33611" class="Bound">Γ</a> <a id="33680" href="plfa.part2.Lambda.html#33468" class="Datatype Operator">⊢</a> <a id="33682" href="plfa.part2.Lambda.html#3812" class="InductiveConstructor Operator">ƛ</a> <a id="33684" href="plfa.part2.Lambda.html#33613" class="Bound">x</a> <a id="33686" href="plfa.part2.Lambda.html#3812" class="InductiveConstructor Operator">⇒</a> <a id="33688" href="plfa.part2.Lambda.html#33615" class="Bound">N</a> <a id="33690" href="plfa.part2.Lambda.html#33468" class="Datatype Operator">⦂</a> <a id="33692" href="plfa.part2.Lambda.html#33617" class="Bound">A</a> <a id="33694" href="plfa.part2.Lambda.html#29431" class="InductiveConstructor Operator">⇒</a> <a id="33696" href="plfa.part2.Lambda.html#33619" class="Bound">B</a>

  <a id="33701" class="Comment">-- ⇒-E</a>
  <a id="_⊢_⦂_._·_"></a><a id="33710" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#33710" class="InductiveConstructor Operator">_·_</a> <a id="33714" class="Symbol">:</a> <a id="33716" class="Symbol">∀</a> <a id="33718" class="Symbol">{</a><a id="33719" href="plfa.part2.Lambda.html#33719" class="Bound">Γ</a> <a id="33721" href="plfa.part2.Lambda.html#33721" class="Bound">L</a> <a id="33723" href="plfa.part2.Lambda.html#33723" class="Bound">M</a> <a id="33725" href="plfa.part2.Lambda.html#33725" class="Bound">A</a> <a id="33727" href="plfa.part2.Lambda.html#33727" class="Bound">B</a><a id="33728" class="Symbol">}</a>
    <a id="33734" class="Symbol">→</a> <a id="33736" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#33719" class="Bound">Γ</a> <a id="33738" href="plfa.part2.Lambda.html#33468" class="Datatype Operator">⊢</a> <a id="33740" href="plfa.part2.Lambda.html#33721" class="Bound">L</a> <a id="33742" href="plfa.part2.Lambda.html#33468" class="Datatype Operator">⦂</a> <a id="33744" href="plfa.part2.Lambda.html#33725" class="Bound">A</a> <a id="33746" href="plfa.part2.Lambda.html#29431" class="InductiveConstructor Operator">⇒</a> <a id="33748" href="plfa.part2.Lambda.html#33727" class="Bound">B</a>
    <a id="33754" class="Symbol">→</a> <a id="33756" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#33719" class="Bound">Γ</a> <a id="33758" href="plfa.part2.Lambda.html#33468" class="Datatype Operator">⊢</a> <a id="33760" href="plfa.part2.Lambda.html#33723" class="Bound">M</a> <a id="33762" href="plfa.part2.Lambda.html#33468" class="Datatype Operator">⦂</a> <a id="33764" href="plfa.part2.Lambda.html#33725" class="Bound">A</a>
      <a id="33772" class="Comment">-------------</a>
    <a id="33790" class="Symbol">→</a> <a id="33792" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#33719" class="Bound">Γ</a> <a id="33794" href="plfa.part2.Lambda.html#33468" class="Datatype Operator">⊢</a> <a id="33796" href="plfa.part2.Lambda.html#33721" class="Bound">L</a> <a id="33798" href="plfa.part2.Lambda.html#3858" class="InductiveConstructor Operator">·</a> <a id="33800" href="plfa.part2.Lambda.html#33723" class="Bound">M</a> <a id="33802" href="plfa.part2.Lambda.html#33468" class="Datatype Operator">⦂</a> <a id="33804" href="plfa.part2.Lambda.html#33727" class="Bound">B</a>

  <a id="33809" class="Comment">-- ℕ-I₁</a>
  <a id="_⊢_⦂_.⊢zero"></a><a id="33819" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#33819" class="InductiveConstructor">⊢zero</a> <a id="33825" class="Symbol">:</a> <a id="33827" class="Symbol">∀</a> <a id="33829" class="Symbol">{</a><a id="33830" href="plfa.part2.Lambda.html#33830" class="Bound">Γ</a><a id="33831" class="Symbol">}</a>
      <a id="33839" class="Comment">--------------</a>
    <a id="33858" class="Symbol">→</a> <a id="33860" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#33830" class="Bound">Γ</a> <a id="33862" href="plfa.part2.Lambda.html#33468" class="Datatype Operator">⊢</a> <a id="33864" href="plfa.part2.Lambda.html#3906" class="InductiveConstructor">`zero</a> <a id="33870" href="plfa.part2.Lambda.html#33468" class="Datatype Operator">⦂</a> <a id="33872" href="plfa.part2.Lambda.html#29458" class="InductiveConstructor">`ℕ</a>

  <a id="33878" class="Comment">-- ℕ-I₂</a>
  <a id="_⊢_⦂_.⊢suc"></a><a id="33888" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#33888" class="InductiveConstructor">⊢suc</a> <a id="33893" class="Symbol">:</a> <a id="33895" class="Symbol">∀</a> <a id="33897" class="Symbol">{</a><a id="33898" href="plfa.part2.Lambda.html#33898" class="Bound">Γ</a> <a id="33900" href="plfa.part2.Lambda.html#33900" class="Bound">M</a><a id="33901" class="Symbol">}</a>
    <a id="33907" class="Symbol">→</a> <a id="33909" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#33898" class="Bound">Γ</a> <a id="33911" href="plfa.part2.Lambda.html#33468" class="Datatype Operator">⊢</a> <a id="33913" href="plfa.part2.Lambda.html#33900" class="Bound">M</a> <a id="33915" href="plfa.part2.Lambda.html#33468" class="Datatype Operator">⦂</a> <a id="33917" href="plfa.part2.Lambda.html#29458" class="InductiveConstructor">`ℕ</a>
      <a id="33926" class="Comment">---------------</a>
    <a id="33946" class="Symbol">→</a> <a id="33948" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#33898" class="Bound">Γ</a> <a id="33950" href="plfa.part2.Lambda.html#33468" class="Datatype Operator">⊢</a> <a id="33952" href="plfa.part2.Lambda.html#3940" class="InductiveConstructor Operator">`suc</a> <a id="33957" href="plfa.part2.Lambda.html#33900" class="Bound">M</a> <a id="33959" href="plfa.part2.Lambda.html#33468" class="Datatype Operator">⦂</a> <a id="33961" href="plfa.part2.Lambda.html#29458" class="InductiveConstructor">`ℕ</a>

  <a id="33967" class="Comment">-- ℕ-E</a>
  <a id="_⊢_⦂_.⊢case"></a><a id="33976" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#33976" class="InductiveConstructor">⊢case</a> <a id="33982" class="Symbol">:</a> <a id="33984" class="Symbol">∀</a> <a id="33986" class="Symbol">{</a><a id="33987" href="plfa.part2.Lambda.html#33987" class="Bound">Γ</a> <a id="33989" href="plfa.part2.Lambda.html#33989" class="Bound">L</a> <a id="33991" href="plfa.part2.Lambda.html#33991" class="Bound">M</a> <a id="33993" href="plfa.part2.Lambda.html#33993" class="Bound">x</a> <a id="33995" href="plfa.part2.Lambda.html#33995" class="Bound">N</a> <a id="33997" href="plfa.part2.Lambda.html#33997" class="Bound">A</a><a id="33998" class="Symbol">}</a>
    <a id="34004" class="Symbol">→</a> <a id="34006" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#33987" class="Bound">Γ</a> <a id="34008" href="plfa.part2.Lambda.html#33468" class="Datatype Operator">⊢</a> <a id="34010" href="plfa.part2.Lambda.html#33989" class="Bound">L</a> <a id="34012" href="plfa.part2.Lambda.html#33468" class="Datatype Operator">⦂</a> <a id="34014" href="plfa.part2.Lambda.html#29458" class="InductiveConstructor">`ℕ</a>
    <a id="34021" class="Symbol">→</a> <a id="34023" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#33987" class="Bound">Γ</a> <a id="34025" href="plfa.part2.Lambda.html#33468" class="Datatype Operator">⊢</a> <a id="34027" href="plfa.part2.Lambda.html#33991" class="Bound">M</a> <a id="34029" href="plfa.part2.Lambda.html#33468" class="Datatype Operator">⦂</a> <a id="34031" href="plfa.part2.Lambda.html#33997" class="Bound">A</a>
    <a id="34037" class="Symbol">→</a> <a id="34039" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#33987" class="Bound">Γ</a> <a id="34041" href="plfa.part2.Lambda.html#31110" class="InductiveConstructor Operator">,</a> <a id="34043" href="plfa.part2.Lambda.html#33993" class="Bound">x</a> <a id="34045" href="plfa.part2.Lambda.html#31110" class="InductiveConstructor Operator">⦂</a> <a id="34047" href="plfa.part2.Lambda.html#29458" class="InductiveConstructor">`ℕ</a> <a id="34050" href="plfa.part2.Lambda.html#33468" class="Datatype Operator">⊢</a> <a id="34052" href="plfa.part2.Lambda.html#33995" class="Bound">N</a> <a id="34054" href="plfa.part2.Lambda.html#33468" class="Datatype Operator">⦂</a> <a id="34056" href="plfa.part2.Lambda.html#33997" class="Bound">A</a>
      <a id="34064" class="Comment">-------------------------------------</a>
    <a id="34106" class="Symbol">→</a> <a id="34108" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#33987" class="Bound">Γ</a> <a id="34110" href="plfa.part2.Lambda.html#33468" class="Datatype Operator">⊢</a> <a id="34112" href="plfa.part2.Lambda.html#3981" class="InductiveConstructor Operator">case</a> <a id="34117" href="plfa.part2.Lambda.html#33989" class="Bound">L</a> <a id="34119" href="plfa.part2.Lambda.html#3981" class="InductiveConstructor Operator">[zero⇒</a> <a id="34126" href="plfa.part2.Lambda.html#33991" class="Bound">M</a> <a id="34128" href="plfa.part2.Lambda.html#3981" class="InductiveConstructor Operator">|suc</a> <a id="34133" href="plfa.part2.Lambda.html#33993" class="Bound">x</a> <a id="34135" href="plfa.part2.Lambda.html#3981" class="InductiveConstructor Operator">⇒</a> <a id="34137" href="plfa.part2.Lambda.html#33995" class="Bound">N</a> <a id="34139" href="plfa.part2.Lambda.html#3981" class="InductiveConstructor Operator">]</a> <a id="34141" href="plfa.part2.Lambda.html#33468" class="Datatype Operator">⦂</a> <a id="34143" href="plfa.part2.Lambda.html#33997" class="Bound">A</a>

  <a id="_⊢_⦂_.⊢μ"></a><a id="34148" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#34148" class="InductiveConstructor">⊢μ</a> <a id="34151" class="Symbol">:</a> <a id="34153" class="Symbol">∀</a> <a id="34155" class="Symbol">{</a><a id="34156" href="plfa.part2.Lambda.html#34156" class="Bound">Γ</a> <a id="34158" href="plfa.part2.Lambda.html#34158" class="Bound">x</a> <a id="34160" href="plfa.part2.Lambda.html#34160" class="Bound">M</a> <a id="34162" href="plfa.part2.Lambda.html#34162" class="Bound">A</a><a id="34163" class="Symbol">}</a>
    <a id="34169" class="Symbol">→</a> <a id="34171" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#34156" class="Bound">Γ</a> <a id="34173" href="plfa.part2.Lambda.html#31110" class="InductiveConstructor Operator">,</a> <a id="34175" href="plfa.part2.Lambda.html#34158" class="Bound">x</a> <a id="34177" href="plfa.part2.Lambda.html#31110" class="InductiveConstructor Operator">⦂</a> <a id="34179" href="plfa.part2.Lambda.html#34162" class="Bound">A</a> <a id="34181" href="plfa.part2.Lambda.html#33468" class="Datatype Operator">⊢</a> <a id="34183" href="plfa.part2.Lambda.html#34160" class="Bound">M</a> <a id="34185" href="plfa.part2.Lambda.html#33468" class="Datatype Operator">⦂</a> <a id="34187" href="plfa.part2.Lambda.html#34162" class="Bound">A</a>
      <a id="34195" class="Comment">-----------------</a>
    <a id="34217" class="Symbol">→</a> <a id="34219" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#34156" class="Bound">Γ</a> <a id="34221" href="plfa.part2.Lambda.html#33468" class="Datatype Operator">⊢</a> <a id="34223" href="plfa.part2.Lambda.html#4041" class="InductiveConstructor Operator">μ</a> <a id="34225" href="plfa.part2.Lambda.html#34158" class="Bound">x</a> <a id="34227" href="plfa.part2.Lambda.html#4041" class="InductiveConstructor Operator">⇒</a> <a id="34229" href="plfa.part2.Lambda.html#34160" class="Bound">M</a> <a id="34231" href="plfa.part2.Lambda.html#33468" class="Datatype Operator">⦂</a> <a id="34233" href="plfa.part2.Lambda.html#34162" class="Bound">A</a>
</pre>{% endraw %}
Each type rule is named after the constructor for the
corresponding term.

Most of the rules have a second name, derived from a convention in
logic, whereby the rule is named after the type connective that it
concerns; rules to introduce and to eliminate each connective are
labeled `-I` and `-E`, respectively. As we read the rules from top to
bottom, introduction and elimination rules do what they say on the
tin: the first _introduces_ a formula for the connective, which
appears in the conclusion but not in the premises; while the second
_eliminates_ a formula for the connective, which appears in a premise
but not in the conclusion. An introduction rule describes how to
construct a value of the type (abstractions yield functions, successor
and zero yield naturals), while an elimination rule describes how to
deconstruct a value of the given type (applications use functions,
case expressions use naturals).

Note also the three places (in `⊢ƛ`, `⊢case`, and `⊢μ`) where the
context is extended with `x` and an appropriate type, corresponding to
the three places where a bound variable is introduced.

The rules are deterministic, in that at most one rule applies to every term.


### Checking inequality and postulating the impossible {#impossible}

The following function makes it convenient to assert an inequality:
{% raw %}<pre class="Agda"><a id="_≠_"></a><a id="35573" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#35573" class="Function Operator">_≠_</a> <a id="35577" class="Symbol">:</a> <a id="35579" class="Symbol">∀</a> <a id="35581" class="Symbol">(</a><a id="35582" href="plfa.part2.Lambda.html#35582" class="Bound">x</a> <a id="35584" href="plfa.part2.Lambda.html#35584" class="Bound">y</a> <a id="35586" class="Symbol">:</a> <a id="35588" href="plfa.part2.Lambda.html#3653" class="Function">Id</a><a id="35590" class="Symbol">)</a> <a id="35592" class="Symbol">→</a> <a id="35594" href="plfa.part2.Lambda.html#35582" class="Bound">x</a> <a id="35596" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#799" class="Function Operator">≢</a> <a id="35598" href="plfa.part2.Lambda.html#35584" class="Bound">y</a>
<a id="35600" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#35600" class="Bound">x</a> <a id="35602" href="plfa.part2.Lambda.html#35573" class="Function Operator">≠</a> <a id="35604" href="plfa.part2.Lambda.html#35604" class="Bound">y</a>  <a id="35607" class="Keyword">with</a> <a id="35612" href="plfa.part2.Lambda.html#35600" class="Bound">x</a> <a id="35614" href="https://agda.github.io/agda-stdlib/v1.1/Data.String.Properties.html#2569" class="Function Operator">≟</a> <a id="35616" href="plfa.part2.Lambda.html#35604" class="Bound">y</a>
<a id="35618" class="Symbol">...</a>       <a id="35628" class="Symbol">|</a> <a id="35630" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#668" class="InductiveConstructor">no</a>  <a id="35634" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#35634" class="Bound">x≢y</a>  <a id="35639" class="Symbol">=</a>  <a id="35642" href="plfa.part2.Lambda.html#35634" class="Bound">x≢y</a>
<a id="35646" class="Symbol">...</a>       <a id="35656" class="Symbol">|</a> <a id="35658" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#641" class="InductiveConstructor">yes</a> <a id="35662" class="Symbol">_</a>    <a id="35667" class="Symbol">=</a>  <a id="35670" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html#294" class="Function">⊥-elim</a> <a id="35677" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#35706" class="Postulate">impossible</a>
  <a id="35690" class="Keyword">where</a> <a id="35696" class="Keyword">postulate</a> <a id="35706" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#35706" class="Postulate">impossible</a> <a id="35717" class="Symbol">:</a> <a id="35719" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html#279" class="Datatype">⊥</a>
</pre>{% endraw %}Here `_≟_` is the function that tests two identifiers for equality.
We intend to apply the function only when the
two arguments are indeed unequal, and indicate that the second
case should never arise by postulating a term `impossible` of
the empty type `⊥`.  If we use C-c C-n to normalise the term

    "a" ≠ "a"

Agda will return an answer warning us that the impossible has occurred:

    ⊥-elim (.plfa.Lambda.impossible "a" "a" refl)

While postulating the impossible is a useful technique, it must be
used with care, since such postulation could allow us to provide
evidence of _any_ proposition whatsoever, regardless of its truth.


### Example type derivations {#derivation}

Type derivations correspond to trees. In informal notation, here
is a type derivation for the Church numeral two,

                            ∋s                     ∋z
                            ------------------ ⊢`  -------------- ⊢`
    ∋s                      Γ₂ ⊢ ` "s" ⦂ A ⇒ A     Γ₂ ⊢ ` "z" ⦂ A
    ------------------ ⊢`   ------------------------------------- _·_
    Γ₂ ⊢ ` "s" ⦂ A ⇒ A      Γ₂ ⊢ ` "s" · ` "z" ⦂ A
    ---------------------------------------------- _·_
    Γ₂ ⊢ ` "s" · (` "s" · ` "z") ⦂ A
    -------------------------------------------- ⊢ƛ
    Γ₁ ⊢ ƛ "z" ⇒ ` "s" · (` "s" · ` "z") ⦂ A ⇒ A
    ------------------------------------------------------------- ⊢ƛ
    Γ ⊢ ƛ "s" ⇒ ƛ "z" ⇒ ` "s" · (` "s" · ` "z") ⦂ (A ⇒ A) ⇒ A ⇒ A

where `∋s` and `∋z` abbreviate the two derivations,

                 ---------------- Z
    "s" ≢ "z"    Γ₁ ∋ "s" ⦂ A ⇒ A
    ----------------------------- S       ------------- Z
    Γ₂ ∋ "s" ⦂ A ⇒ A                       Γ₂ ∋ "z" ⦂ A

and where `Γ₁ = Γ , "s" ⦂ A ⇒ A` and `Γ₂ = Γ , "s" ⦂ A ⇒ A , "z" ⦂ A`.
The typing derivation is valid for any `Γ` and `A`, for instance,
we might take `Γ` to be `∅` and `A` to be `` `ℕ ``.

Here is the above typing derivation formalised in Agda:
{% raw %}<pre class="Agda"><a id="Ch"></a><a id="37652" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#37652" class="Function">Ch</a> <a id="37655" class="Symbol">:</a> <a id="37657" href="plfa.part2.Lambda.html#29412" class="Datatype">Type</a> <a id="37662" class="Symbol">→</a> <a id="37664" href="plfa.part2.Lambda.html#29412" class="Datatype">Type</a>
<a id="37669" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#37652" class="Function">Ch</a> <a id="37672" href="plfa.part2.Lambda.html#37672" class="Bound">A</a> <a id="37674" class="Symbol">=</a> <a id="37676" class="Symbol">(</a><a id="37677" href="plfa.part2.Lambda.html#37672" class="Bound">A</a> <a id="37679" href="plfa.part2.Lambda.html#29431" class="InductiveConstructor Operator">⇒</a> <a id="37681" href="plfa.part2.Lambda.html#37672" class="Bound">A</a><a id="37682" class="Symbol">)</a> <a id="37684" href="plfa.part2.Lambda.html#29431" class="InductiveConstructor Operator">⇒</a> <a id="37686" href="plfa.part2.Lambda.html#37672" class="Bound">A</a> <a id="37688" href="plfa.part2.Lambda.html#29431" class="InductiveConstructor Operator">⇒</a> <a id="37690" href="plfa.part2.Lambda.html#37672" class="Bound">A</a>

<a id="⊢twoᶜ"></a><a id="37693" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#37693" class="Function">⊢twoᶜ</a> <a id="37699" class="Symbol">:</a> <a id="37701" class="Symbol">∀</a> <a id="37703" class="Symbol">{</a><a id="37704" href="plfa.part2.Lambda.html#37704" class="Bound">Γ</a> <a id="37706" href="plfa.part2.Lambda.html#37706" class="Bound">A</a><a id="37707" class="Symbol">}</a> <a id="37709" class="Symbol">→</a> <a id="37711" href="plfa.part2.Lambda.html#37704" class="Bound">Γ</a> <a id="37713" href="plfa.part2.Lambda.html#33468" class="Datatype Operator">⊢</a> <a id="37715" href="plfa.part2.Lambda.html#5731" class="Function">twoᶜ</a> <a id="37720" href="plfa.part2.Lambda.html#33468" class="Datatype Operator">⦂</a> <a id="37722" href="plfa.part2.Lambda.html#37652" class="Function">Ch</a> <a id="37725" href="plfa.part2.Lambda.html#37706" class="Bound">A</a>
<a id="37727" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#37693" class="Function">⊢twoᶜ</a> <a id="37733" class="Symbol">=</a> <a id="37735" href="plfa.part2.Lambda.html#33603" class="InductiveConstructor">⊢ƛ</a> <a id="37738" class="Symbol">(</a><a id="37739" href="plfa.part2.Lambda.html#33603" class="InductiveConstructor">⊢ƛ</a> <a id="37742" class="Symbol">(</a><a id="37743" href="plfa.part2.Lambda.html#33524" class="InductiveConstructor">⊢`</a> <a id="37746" href="plfa.part2.Lambda.html#37779" class="Function">∋s</a> <a id="37749" href="plfa.part2.Lambda.html#33710" class="InductiveConstructor Operator">·</a> <a id="37751" class="Symbol">(</a><a id="37752" href="plfa.part2.Lambda.html#33524" class="InductiveConstructor">⊢`</a> <a id="37755" href="plfa.part2.Lambda.html#37779" class="Function">∋s</a> <a id="37758" href="plfa.part2.Lambda.html#33710" class="InductiveConstructor Operator">·</a> <a id="37760" href="plfa.part2.Lambda.html#33524" class="InductiveConstructor">⊢`</a> <a id="37763" href="plfa.part2.Lambda.html#37802" class="Function">∋z</a><a id="37765" class="Symbol">)))</a>
  <a id="37771" class="Keyword">where</a>
  <a id="37779" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#37779" class="Function">∋s</a> <a id="37782" class="Symbol">=</a> <a id="37784" href="plfa.part2.Lambda.html#32413" class="InductiveConstructor">S</a> <a id="37786" class="Symbol">(</a><a id="37787" class="String">&quot;s&quot;</a> <a id="37791" href="plfa.part2.Lambda.html#35573" class="Function Operator">≠</a> <a id="37793" class="String">&quot;z&quot;</a><a id="37796" class="Symbol">)</a> <a id="37798" href="plfa.part2.Lambda.html#32347" class="InductiveConstructor">Z</a>
  <a id="37802" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#37802" class="Function">∋z</a> <a id="37805" class="Symbol">=</a> <a id="37807" href="plfa.part2.Lambda.html#32347" class="InductiveConstructor">Z</a>
</pre>{% endraw %}
Here are the typings corresponding to computing two plus two:
{% raw %}<pre class="Agda"><a id="⊢two"></a><a id="37880" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#37880" class="Function">⊢two</a> <a id="37885" class="Symbol">:</a> <a id="37887" class="Symbol">∀</a> <a id="37889" class="Symbol">{</a><a id="37890" href="plfa.part2.Lambda.html#37890" class="Bound">Γ</a><a id="37891" class="Symbol">}</a> <a id="37893" class="Symbol">→</a> <a id="37895" href="plfa.part2.Lambda.html#37890" class="Bound">Γ</a> <a id="37897" href="plfa.part2.Lambda.html#33468" class="Datatype Operator">⊢</a> <a id="37899" href="plfa.part2.Lambda.html#4482" class="Function">two</a> <a id="37903" href="plfa.part2.Lambda.html#33468" class="Datatype Operator">⦂</a> <a id="37905" href="plfa.part2.Lambda.html#29458" class="InductiveConstructor">`ℕ</a>
<a id="37908" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#37880" class="Function">⊢two</a> <a id="37913" class="Symbol">=</a> <a id="37915" href="plfa.part2.Lambda.html#33888" class="InductiveConstructor">⊢suc</a> <a id="37920" class="Symbol">(</a><a id="37921" href="plfa.part2.Lambda.html#33888" class="InductiveConstructor">⊢suc</a> <a id="37926" href="plfa.part2.Lambda.html#33819" class="InductiveConstructor">⊢zero</a><a id="37931" class="Symbol">)</a>

<a id="⊢plus"></a><a id="37934" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#37934" class="Function">⊢plus</a> <a id="37940" class="Symbol">:</a> <a id="37942" class="Symbol">∀</a> <a id="37944" class="Symbol">{</a><a id="37945" href="plfa.part2.Lambda.html#37945" class="Bound">Γ</a><a id="37946" class="Symbol">}</a> <a id="37948" class="Symbol">→</a> <a id="37950" href="plfa.part2.Lambda.html#37945" class="Bound">Γ</a> <a id="37952" href="plfa.part2.Lambda.html#33468" class="Datatype Operator">⊢</a> <a id="37954" href="plfa.part2.Lambda.html#4516" class="Function">plus</a> <a id="37959" href="plfa.part2.Lambda.html#33468" class="Datatype Operator">⦂</a> <a id="37961" href="plfa.part2.Lambda.html#29458" class="InductiveConstructor">`ℕ</a> <a id="37964" href="plfa.part2.Lambda.html#29431" class="InductiveConstructor Operator">⇒</a> <a id="37966" href="plfa.part2.Lambda.html#29458" class="InductiveConstructor">`ℕ</a> <a id="37969" href="plfa.part2.Lambda.html#29431" class="InductiveConstructor Operator">⇒</a> <a id="37971" href="plfa.part2.Lambda.html#29458" class="InductiveConstructor">`ℕ</a>
<a id="37974" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#37934" class="Function">⊢plus</a> <a id="37980" class="Symbol">=</a> <a id="37982" href="plfa.part2.Lambda.html#34148" class="InductiveConstructor">⊢μ</a> <a id="37985" class="Symbol">(</a><a id="37986" href="plfa.part2.Lambda.html#33603" class="InductiveConstructor">⊢ƛ</a> <a id="37989" class="Symbol">(</a><a id="37990" href="plfa.part2.Lambda.html#33603" class="InductiveConstructor">⊢ƛ</a> <a id="37993" class="Symbol">(</a><a id="37994" href="plfa.part2.Lambda.html#33976" class="InductiveConstructor">⊢case</a> <a id="38000" class="Symbol">(</a><a id="38001" href="plfa.part2.Lambda.html#33524" class="InductiveConstructor">⊢`</a> <a id="38004" href="plfa.part2.Lambda.html#38129" class="Function">∋m</a><a id="38006" class="Symbol">)</a> <a id="38008" class="Symbol">(</a><a id="38009" href="plfa.part2.Lambda.html#33524" class="InductiveConstructor">⊢`</a> <a id="38012" href="plfa.part2.Lambda.html#38155" class="Function">∋n</a><a id="38014" class="Symbol">)</a>
         <a id="38025" class="Symbol">(</a><a id="38026" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#33888" class="InductiveConstructor">⊢suc</a> <a id="38031" class="Symbol">(</a><a id="38032" href="plfa.part2.Lambda.html#33524" class="InductiveConstructor">⊢`</a> <a id="38035" href="plfa.part2.Lambda.html#38071" class="Function">∋+</a> <a id="38038" href="plfa.part2.Lambda.html#33710" class="InductiveConstructor Operator">·</a> <a id="38040" href="plfa.part2.Lambda.html#33524" class="InductiveConstructor">⊢`</a> <a id="38043" href="plfa.part2.Lambda.html#38165" class="Function">∋m′</a> <a id="38047" href="plfa.part2.Lambda.html#33710" class="InductiveConstructor Operator">·</a> <a id="38049" href="plfa.part2.Lambda.html#33524" class="InductiveConstructor">⊢`</a> <a id="38052" href="plfa.part2.Lambda.html#38175" class="Function">∋n′</a><a id="38055" class="Symbol">)))))</a>
  <a id="38063" class="Keyword">where</a>
  <a id="38071" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#38071" class="Function">∋+</a>  <a id="38075" class="Symbol">=</a> <a id="38077" class="Symbol">(</a><a id="38078" href="plfa.part2.Lambda.html#32413" class="InductiveConstructor">S</a> <a id="38080" class="Symbol">(</a><a id="38081" class="String">&quot;+&quot;</a> <a id="38085" href="plfa.part2.Lambda.html#35573" class="Function Operator">≠</a> <a id="38087" class="String">&quot;m&quot;</a><a id="38090" class="Symbol">)</a> <a id="38092" class="Symbol">(</a><a id="38093" href="plfa.part2.Lambda.html#32413" class="InductiveConstructor">S</a> <a id="38095" class="Symbol">(</a><a id="38096" class="String">&quot;+&quot;</a> <a id="38100" href="plfa.part2.Lambda.html#35573" class="Function Operator">≠</a> <a id="38102" class="String">&quot;n&quot;</a><a id="38105" class="Symbol">)</a> <a id="38107" class="Symbol">(</a><a id="38108" href="plfa.part2.Lambda.html#32413" class="InductiveConstructor">S</a> <a id="38110" class="Symbol">(</a><a id="38111" class="String">&quot;+&quot;</a> <a id="38115" href="plfa.part2.Lambda.html#35573" class="Function Operator">≠</a> <a id="38117" class="String">&quot;m&quot;</a><a id="38120" class="Symbol">)</a> <a id="38122" href="plfa.part2.Lambda.html#32347" class="InductiveConstructor">Z</a><a id="38123" class="Symbol">)))</a>
  <a id="38129" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#38129" class="Function">∋m</a>  <a id="38133" class="Symbol">=</a> <a id="38135" class="Symbol">(</a><a id="38136" href="plfa.part2.Lambda.html#32413" class="InductiveConstructor">S</a> <a id="38138" class="Symbol">(</a><a id="38139" class="String">&quot;m&quot;</a> <a id="38143" href="plfa.part2.Lambda.html#35573" class="Function Operator">≠</a> <a id="38145" class="String">&quot;n&quot;</a><a id="38148" class="Symbol">)</a> <a id="38150" href="plfa.part2.Lambda.html#32347" class="InductiveConstructor">Z</a><a id="38151" class="Symbol">)</a>
  <a id="38155" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#38155" class="Function">∋n</a>  <a id="38159" class="Symbol">=</a> <a id="38161" href="plfa.part2.Lambda.html#32347" class="InductiveConstructor">Z</a>
  <a id="38165" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#38165" class="Function">∋m′</a> <a id="38169" class="Symbol">=</a> <a id="38171" href="plfa.part2.Lambda.html#32347" class="InductiveConstructor">Z</a>
  <a id="38175" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#38175" class="Function">∋n′</a> <a id="38179" class="Symbol">=</a> <a id="38181" class="Symbol">(</a><a id="38182" href="plfa.part2.Lambda.html#32413" class="InductiveConstructor">S</a> <a id="38184" class="Symbol">(</a><a id="38185" class="String">&quot;n&quot;</a> <a id="38189" href="plfa.part2.Lambda.html#35573" class="Function Operator">≠</a> <a id="38191" class="String">&quot;m&quot;</a><a id="38194" class="Symbol">)</a> <a id="38196" href="plfa.part2.Lambda.html#32347" class="InductiveConstructor">Z</a><a id="38197" class="Symbol">)</a>

<a id="⊢2+2"></a><a id="38200" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#38200" class="Function">⊢2+2</a> <a id="38205" class="Symbol">:</a> <a id="38207" href="plfa.part2.Lambda.html#31092" class="InductiveConstructor">∅</a> <a id="38209" href="plfa.part2.Lambda.html#33468" class="Datatype Operator">⊢</a> <a id="38211" href="plfa.part2.Lambda.html#4516" class="Function">plus</a> <a id="38216" href="plfa.part2.Lambda.html#3858" class="InductiveConstructor Operator">·</a> <a id="38218" href="plfa.part2.Lambda.html#4482" class="Function">two</a> <a id="38222" href="plfa.part2.Lambda.html#3858" class="InductiveConstructor Operator">·</a> <a id="38224" href="plfa.part2.Lambda.html#4482" class="Function">two</a> <a id="38228" href="plfa.part2.Lambda.html#33468" class="Datatype Operator">⦂</a> <a id="38230" href="plfa.part2.Lambda.html#29458" class="InductiveConstructor">`ℕ</a>
<a id="38233" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#38200" class="Function">⊢2+2</a> <a id="38238" class="Symbol">=</a> <a id="38240" href="plfa.part2.Lambda.html#37934" class="Function">⊢plus</a> <a id="38246" href="plfa.part2.Lambda.html#33710" class="InductiveConstructor Operator">·</a> <a id="38248" href="plfa.part2.Lambda.html#37880" class="Function">⊢two</a> <a id="38253" href="plfa.part2.Lambda.html#33710" class="InductiveConstructor Operator">·</a> <a id="38255" href="plfa.part2.Lambda.html#37880" class="Function">⊢two</a>
</pre>{% endraw %}In contrast to our earlier examples, here we have typed `two` and `plus`
in an arbitrary context rather than the empty context; this makes it easy
to use them inside other binding contexts as well as at the top level.
Here the two lookup judgments `∋m` and `∋m′` refer to two different
bindings of variables named `"m"`.  In contrast, the two judgments `∋n` and
`∋n′` both refer to the same binding of `"n"` but accessed in different
contexts, the first where "n" is the last binding in the context, and
the second after "m" is bound in the successor branch of the case.

And here are typings for the remainder of the Church example:
{% raw %}<pre class="Agda"><a id="⊢plusᶜ"></a><a id="38902" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#38902" class="Function">⊢plusᶜ</a> <a id="38909" class="Symbol">:</a> <a id="38911" class="Symbol">∀</a> <a id="38913" class="Symbol">{</a><a id="38914" href="plfa.part2.Lambda.html#38914" class="Bound">Γ</a> <a id="38916" href="plfa.part2.Lambda.html#38916" class="Bound">A</a><a id="38917" class="Symbol">}</a> <a id="38919" class="Symbol">→</a> <a id="38921" href="plfa.part2.Lambda.html#38914" class="Bound">Γ</a>  <a id="38924" href="plfa.part2.Lambda.html#33468" class="Datatype Operator">⊢</a> <a id="38926" href="plfa.part2.Lambda.html#5792" class="Function">plusᶜ</a> <a id="38932" href="plfa.part2.Lambda.html#33468" class="Datatype Operator">⦂</a> <a id="38934" href="plfa.part2.Lambda.html#37652" class="Function">Ch</a> <a id="38937" href="plfa.part2.Lambda.html#38916" class="Bound">A</a> <a id="38939" href="plfa.part2.Lambda.html#29431" class="InductiveConstructor Operator">⇒</a> <a id="38941" href="plfa.part2.Lambda.html#37652" class="Function">Ch</a> <a id="38944" href="plfa.part2.Lambda.html#38916" class="Bound">A</a> <a id="38946" href="plfa.part2.Lambda.html#29431" class="InductiveConstructor Operator">⇒</a> <a id="38948" href="plfa.part2.Lambda.html#37652" class="Function">Ch</a> <a id="38951" href="plfa.part2.Lambda.html#38916" class="Bound">A</a>
<a id="38953" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#38902" class="Function">⊢plusᶜ</a> <a id="38960" class="Symbol">=</a> <a id="38962" href="plfa.part2.Lambda.html#33603" class="InductiveConstructor">⊢ƛ</a> <a id="38965" class="Symbol">(</a><a id="38966" href="plfa.part2.Lambda.html#33603" class="InductiveConstructor">⊢ƛ</a> <a id="38969" class="Symbol">(</a><a id="38970" href="plfa.part2.Lambda.html#33603" class="InductiveConstructor">⊢ƛ</a> <a id="38973" class="Symbol">(</a><a id="38974" href="plfa.part2.Lambda.html#33603" class="InductiveConstructor">⊢ƛ</a> <a id="38977" class="Symbol">(</a><a id="38978" href="plfa.part2.Lambda.html#33524" class="InductiveConstructor">⊢`</a> <a id="38981" href="plfa.part2.Lambda.html#39032" class="Function">∋m</a> <a id="38984" href="plfa.part2.Lambda.html#33710" class="InductiveConstructor Operator">·</a> <a id="38986" href="plfa.part2.Lambda.html#33524" class="InductiveConstructor">⊢`</a> <a id="38989" href="plfa.part2.Lambda.html#39126" class="Function">∋s</a> <a id="38992" href="plfa.part2.Lambda.html#33710" class="InductiveConstructor Operator">·</a> <a id="38994" class="Symbol">(</a><a id="38995" href="plfa.part2.Lambda.html#33524" class="InductiveConstructor">⊢`</a> <a id="38998" href="plfa.part2.Lambda.html#39087" class="Function">∋n</a> <a id="39001" href="plfa.part2.Lambda.html#33710" class="InductiveConstructor Operator">·</a> <a id="39003" href="plfa.part2.Lambda.html#33524" class="InductiveConstructor">⊢`</a> <a id="39006" href="plfa.part2.Lambda.html#39126" class="Function">∋s</a> <a id="39009" href="plfa.part2.Lambda.html#33710" class="InductiveConstructor Operator">·</a> <a id="39011" href="plfa.part2.Lambda.html#33524" class="InductiveConstructor">⊢`</a> <a id="39014" href="plfa.part2.Lambda.html#39149" class="Function">∋z</a><a id="39016" class="Symbol">)))))</a>
  <a id="39024" class="Keyword">where</a>
  <a id="39032" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#39032" class="Function">∋m</a> <a id="39035" class="Symbol">=</a> <a id="39037" href="plfa.part2.Lambda.html#32413" class="InductiveConstructor">S</a> <a id="39039" class="Symbol">(</a><a id="39040" class="String">&quot;m&quot;</a> <a id="39044" href="plfa.part2.Lambda.html#35573" class="Function Operator">≠</a> <a id="39046" class="String">&quot;z&quot;</a><a id="39049" class="Symbol">)</a> <a id="39051" class="Symbol">(</a><a id="39052" href="plfa.part2.Lambda.html#32413" class="InductiveConstructor">S</a> <a id="39054" class="Symbol">(</a><a id="39055" class="String">&quot;m&quot;</a> <a id="39059" href="plfa.part2.Lambda.html#35573" class="Function Operator">≠</a> <a id="39061" class="String">&quot;s&quot;</a><a id="39064" class="Symbol">)</a> <a id="39066" class="Symbol">(</a><a id="39067" href="plfa.part2.Lambda.html#32413" class="InductiveConstructor">S</a> <a id="39069" class="Symbol">(</a><a id="39070" class="String">&quot;m&quot;</a> <a id="39074" href="plfa.part2.Lambda.html#35573" class="Function Operator">≠</a> <a id="39076" class="String">&quot;n&quot;</a><a id="39079" class="Symbol">)</a> <a id="39081" href="plfa.part2.Lambda.html#32347" class="InductiveConstructor">Z</a><a id="39082" class="Symbol">))</a>
  <a id="39087" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#39087" class="Function">∋n</a> <a id="39090" class="Symbol">=</a> <a id="39092" href="plfa.part2.Lambda.html#32413" class="InductiveConstructor">S</a> <a id="39094" class="Symbol">(</a><a id="39095" class="String">&quot;n&quot;</a> <a id="39099" href="plfa.part2.Lambda.html#35573" class="Function Operator">≠</a> <a id="39101" class="String">&quot;z&quot;</a><a id="39104" class="Symbol">)</a> <a id="39106" class="Symbol">(</a><a id="39107" href="plfa.part2.Lambda.html#32413" class="InductiveConstructor">S</a> <a id="39109" class="Symbol">(</a><a id="39110" class="String">&quot;n&quot;</a> <a id="39114" href="plfa.part2.Lambda.html#35573" class="Function Operator">≠</a> <a id="39116" class="String">&quot;s&quot;</a><a id="39119" class="Symbol">)</a> <a id="39121" href="plfa.part2.Lambda.html#32347" class="InductiveConstructor">Z</a><a id="39122" class="Symbol">)</a>
  <a id="39126" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#39126" class="Function">∋s</a> <a id="39129" class="Symbol">=</a> <a id="39131" href="plfa.part2.Lambda.html#32413" class="InductiveConstructor">S</a> <a id="39133" class="Symbol">(</a><a id="39134" class="String">&quot;s&quot;</a> <a id="39138" href="plfa.part2.Lambda.html#35573" class="Function Operator">≠</a> <a id="39140" class="String">&quot;z&quot;</a><a id="39143" class="Symbol">)</a> <a id="39145" href="plfa.part2.Lambda.html#32347" class="InductiveConstructor">Z</a>
  <a id="39149" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#39149" class="Function">∋z</a> <a id="39152" class="Symbol">=</a> <a id="39154" href="plfa.part2.Lambda.html#32347" class="InductiveConstructor">Z</a>

<a id="⊢sucᶜ"></a><a id="39157" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#39157" class="Function">⊢sucᶜ</a> <a id="39163" class="Symbol">:</a> <a id="39165" class="Symbol">∀</a> <a id="39167" class="Symbol">{</a><a id="39168" href="plfa.part2.Lambda.html#39168" class="Bound">Γ</a><a id="39169" class="Symbol">}</a> <a id="39171" class="Symbol">→</a> <a id="39173" href="plfa.part2.Lambda.html#39168" class="Bound">Γ</a> <a id="39175" href="plfa.part2.Lambda.html#33468" class="Datatype Operator">⊢</a> <a id="39177" href="plfa.part2.Lambda.html#5896" class="Function">sucᶜ</a> <a id="39182" href="plfa.part2.Lambda.html#33468" class="Datatype Operator">⦂</a> <a id="39184" href="plfa.part2.Lambda.html#29458" class="InductiveConstructor">`ℕ</a> <a id="39187" href="plfa.part2.Lambda.html#29431" class="InductiveConstructor Operator">⇒</a> <a id="39189" href="plfa.part2.Lambda.html#29458" class="InductiveConstructor">`ℕ</a>
<a id="39192" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#39157" class="Function">⊢sucᶜ</a> <a id="39198" class="Symbol">=</a> <a id="39200" href="plfa.part2.Lambda.html#33603" class="InductiveConstructor">⊢ƛ</a> <a id="39203" class="Symbol">(</a><a id="39204" href="plfa.part2.Lambda.html#33888" class="InductiveConstructor">⊢suc</a> <a id="39209" class="Symbol">(</a><a id="39210" href="plfa.part2.Lambda.html#33524" class="InductiveConstructor">⊢`</a> <a id="39213" href="plfa.part2.Lambda.html#39228" class="Function">∋n</a><a id="39215" class="Symbol">))</a>
  <a id="39220" class="Keyword">where</a>
  <a id="39228" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#39228" class="Function">∋n</a> <a id="39231" class="Symbol">=</a> <a id="39233" href="plfa.part2.Lambda.html#32347" class="InductiveConstructor">Z</a>

<a id="⊢2+2ᶜ"></a><a id="39236" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#39236" class="Function">⊢2+2ᶜ</a> <a id="39242" class="Symbol">:</a> <a id="39244" href="plfa.part2.Lambda.html#31092" class="InductiveConstructor">∅</a> <a id="39246" href="plfa.part2.Lambda.html#33468" class="Datatype Operator">⊢</a> <a id="39248" href="plfa.part2.Lambda.html#5792" class="Function">plusᶜ</a> <a id="39254" href="plfa.part2.Lambda.html#3858" class="InductiveConstructor Operator">·</a> <a id="39256" href="plfa.part2.Lambda.html#5731" class="Function">twoᶜ</a> <a id="39261" href="plfa.part2.Lambda.html#3858" class="InductiveConstructor Operator">·</a> <a id="39263" href="plfa.part2.Lambda.html#5731" class="Function">twoᶜ</a> <a id="39268" href="plfa.part2.Lambda.html#3858" class="InductiveConstructor Operator">·</a> <a id="39270" href="plfa.part2.Lambda.html#5896" class="Function">sucᶜ</a> <a id="39275" href="plfa.part2.Lambda.html#3858" class="InductiveConstructor Operator">·</a> <a id="39277" href="plfa.part2.Lambda.html#3906" class="InductiveConstructor">`zero</a> <a id="39283" href="plfa.part2.Lambda.html#33468" class="Datatype Operator">⦂</a> <a id="39285" href="plfa.part2.Lambda.html#29458" class="InductiveConstructor">`ℕ</a>
<a id="39288" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#39236" class="Function">⊢2+2ᶜ</a> <a id="39294" class="Symbol">=</a> <a id="39296" href="plfa.part2.Lambda.html#38902" class="Function">⊢plusᶜ</a> <a id="39303" href="plfa.part2.Lambda.html#33710" class="InductiveConstructor Operator">·</a> <a id="39305" href="plfa.part2.Lambda.html#37693" class="Function">⊢twoᶜ</a> <a id="39311" href="plfa.part2.Lambda.html#33710" class="InductiveConstructor Operator">·</a> <a id="39313" href="plfa.part2.Lambda.html#37693" class="Function">⊢twoᶜ</a> <a id="39319" href="plfa.part2.Lambda.html#33710" class="InductiveConstructor Operator">·</a> <a id="39321" href="plfa.part2.Lambda.html#39157" class="Function">⊢sucᶜ</a> <a id="39327" href="plfa.part2.Lambda.html#33710" class="InductiveConstructor Operator">·</a> <a id="39329" href="plfa.part2.Lambda.html#33819" class="InductiveConstructor">⊢zero</a>
</pre>{% endraw %}
### Interaction with Agda

Construction of a type derivation may be done interactively.
Start with the declaration:

    ⊢sucᶜ : ∅ ⊢ sucᶜ ⦂ `ℕ ⇒ `ℕ
    ⊢sucᶜ = ?

Typing C-c C-l causes Agda to create a hole and tell us its expected type:

    ⊢sucᶜ = { }0
    ?0 : ∅ ⊢ sucᶜ ⦂ `ℕ ⇒ `ℕ

Now we fill in the hole by typing C-c C-r. Agda observes that
the outermost term in `sucᶜ` is `ƛ`, which is typed using `⊢ƛ`. The
`⊢ƛ` rule in turn takes one argument, which Agda leaves as a hole:

    ⊢sucᶜ = ⊢ƛ { }1
    ?1 : ∅ , "n" ⦂ `ℕ ⊢ `suc ` "n" ⦂ `ℕ

We can fill in the hole by typing C-c C-r again:

    ⊢sucᶜ = ⊢ƛ (⊢suc { }2)
    ?2 : ∅ , "n" ⦂ `ℕ ⊢ ` "n" ⦂ `ℕ

And again:

    ⊢suc′ = ⊢ƛ (⊢suc (⊢` { }3))
    ?3 : ∅ , "n" ⦂ `ℕ ∋ "n" ⦂ `ℕ

A further attempt with C-c C-r yields the message:

    Don't know which constructor to introduce of Z or S

We can fill in `Z` by hand. If we type C-c C-space, Agda will confirm we are done:

    ⊢suc′ = ⊢ƛ (⊢suc (⊢` Z))

The entire process can be automated using Agsy, invoked with C-c C-a.

Chapter [Inference]({{ site.baseurl }}/Inference/)
will show how to use Agda to compute type derivations directly.


### Lookup is injective

The lookup relation `Γ ∋ x ⦂ A` is injective, in that for each `Γ` and `x`
there is at most one `A` such that the judgment holds:
{% raw %}<pre class="Agda"><a id="∋-injective"></a><a id="40645" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#40645" class="Function">∋-injective</a> <a id="40657" class="Symbol">:</a> <a id="40659" class="Symbol">∀</a> <a id="40661" class="Symbol">{</a><a id="40662" href="plfa.part2.Lambda.html#40662" class="Bound">Γ</a> <a id="40664" href="plfa.part2.Lambda.html#40664" class="Bound">x</a> <a id="40666" href="plfa.part2.Lambda.html#40666" class="Bound">A</a> <a id="40668" href="plfa.part2.Lambda.html#40668" class="Bound">B</a><a id="40669" class="Symbol">}</a> <a id="40671" class="Symbol">→</a> <a id="40673" href="plfa.part2.Lambda.html#40662" class="Bound">Γ</a> <a id="40675" href="plfa.part2.Lambda.html#32304" class="Datatype Operator">∋</a> <a id="40677" href="plfa.part2.Lambda.html#40664" class="Bound">x</a> <a id="40679" href="plfa.part2.Lambda.html#32304" class="Datatype Operator">⦂</a> <a id="40681" href="plfa.part2.Lambda.html#40666" class="Bound">A</a> <a id="40683" class="Symbol">→</a> <a id="40685" href="plfa.part2.Lambda.html#40662" class="Bound">Γ</a> <a id="40687" href="plfa.part2.Lambda.html#32304" class="Datatype Operator">∋</a> <a id="40689" href="plfa.part2.Lambda.html#40664" class="Bound">x</a> <a id="40691" href="plfa.part2.Lambda.html#32304" class="Datatype Operator">⦂</a> <a id="40693" href="plfa.part2.Lambda.html#40668" class="Bound">B</a> <a id="40695" class="Symbol">→</a> <a id="40697" href="plfa.part2.Lambda.html#40666" class="Bound">A</a> <a id="40699" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="40701" href="plfa.part2.Lambda.html#40668" class="Bound">B</a>
<a id="40703" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#40645" class="Function">∋-injective</a> <a id="40715" href="plfa.part2.Lambda.html#32347" class="InductiveConstructor">Z</a>        <a id="40724" href="plfa.part2.Lambda.html#32347" class="InductiveConstructor">Z</a>          <a id="40735" class="Symbol">=</a>  <a id="40738" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>
<a id="40743" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#40645" class="Function">∋-injective</a> <a id="40755" href="plfa.part2.Lambda.html#32347" class="InductiveConstructor">Z</a>        <a id="40764" class="Symbol">(</a><a id="40765" href="plfa.part2.Lambda.html#32413" class="InductiveConstructor">S</a> <a id="40767" href="plfa.part2.Lambda.html#40767" class="Bound">x≢</a> <a id="40770" class="Symbol">_)</a>   <a id="40775" class="Symbol">=</a>  <a id="40778" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html#294" class="Function">⊥-elim</a> <a id="40785" class="Symbol">(</a><a id="40786" href="plfa.part2.Lambda.html#40767" class="Bound">x≢</a> <a id="40789" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a><a id="40793" class="Symbol">)</a>
<a id="40795" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#40645" class="Function">∋-injective</a> <a id="40807" class="Symbol">(</a><a id="40808" href="plfa.part2.Lambda.html#32413" class="InductiveConstructor">S</a> <a id="40810" href="plfa.part2.Lambda.html#40810" class="Bound">x≢</a> <a id="40813" class="Symbol">_)</a> <a id="40816" href="plfa.part2.Lambda.html#32347" class="InductiveConstructor">Z</a>          <a id="40827" class="Symbol">=</a>  <a id="40830" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html#294" class="Function">⊥-elim</a> <a id="40837" class="Symbol">(</a><a id="40838" href="plfa.part2.Lambda.html#40810" class="Bound">x≢</a> <a id="40841" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a><a id="40845" class="Symbol">)</a>
<a id="40847" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#40645" class="Function">∋-injective</a> <a id="40859" class="Symbol">(</a><a id="40860" href="plfa.part2.Lambda.html#32413" class="InductiveConstructor">S</a> <a id="40862" class="Symbol">_</a> <a id="40864" href="plfa.part2.Lambda.html#40864" class="Bound">∋x</a><a id="40866" class="Symbol">)</a> <a id="40868" class="Symbol">(</a><a id="40869" href="plfa.part2.Lambda.html#32413" class="InductiveConstructor">S</a> <a id="40871" class="Symbol">_</a> <a id="40873" href="plfa.part2.Lambda.html#40873" class="Bound">∋x′</a><a id="40876" class="Symbol">)</a>  <a id="40879" class="Symbol">=</a>  <a id="40882" href="plfa.part2.Lambda.html#40645" class="Function">∋-injective</a> <a id="40894" href="plfa.part2.Lambda.html#40864" class="Bound">∋x</a> <a id="40897" href="plfa.part2.Lambda.html#40873" class="Bound">∋x′</a>
</pre>{% endraw %}
The typing relation `Γ ⊢ M ⦂ A` is not injective. For example, in any `Γ`
the term `ƛ "x" ⇒ "x"` has type `A ⇒ A` for any type `A`.

### Non-examples

We can also show that terms are _not_ typeable.  For example, here is
a formal proof that it is not possible to type the term
`` `zero · `suc `zero ``.  It cannot be typed, because doing so
requires that the first term in the application is both a natural and
a function:

{% raw %}<pre class="Agda"><a id="nope₁"></a><a id="41334" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#41334" class="Function">nope₁</a> <a id="41340" class="Symbol">:</a> <a id="41342" class="Symbol">∀</a> <a id="41344" class="Symbol">{</a><a id="41345" href="plfa.part2.Lambda.html#41345" class="Bound">A</a><a id="41346" class="Symbol">}</a> <a id="41348" class="Symbol">→</a> <a id="41350" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#535" class="Function Operator">¬</a> <a id="41352" class="Symbol">(</a><a id="41353" href="plfa.part2.Lambda.html#31092" class="InductiveConstructor">∅</a> <a id="41355" href="plfa.part2.Lambda.html#33468" class="Datatype Operator">⊢</a> <a id="41357" href="plfa.part2.Lambda.html#3906" class="InductiveConstructor">`zero</a> <a id="41363" href="plfa.part2.Lambda.html#3858" class="InductiveConstructor Operator">·</a> <a id="41365" href="plfa.part2.Lambda.html#3940" class="InductiveConstructor Operator">`suc</a> <a id="41370" href="plfa.part2.Lambda.html#3906" class="InductiveConstructor">`zero</a> <a id="41376" href="plfa.part2.Lambda.html#33468" class="Datatype Operator">⦂</a> <a id="41378" href="plfa.part2.Lambda.html#41345" class="Bound">A</a><a id="41379" class="Symbol">)</a>
<a id="41381" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#41334" class="Function">nope₁</a> <a id="41387" class="Symbol">(()</a> <a id="41391" href="plfa.part2.Lambda.html#33710" class="InductiveConstructor Operator">·</a> <a id="41393" class="Symbol">_)</a>
</pre>{% endraw %}
As a second example, here is a formal proof that it is not possible to
type `` ƛ "x" ⇒ ` "x" · ` "x" ``. It cannot be typed, because
doing so requires types `A` and `B` such that `A ⇒ B ≡ A`:

{% raw %}<pre class="Agda"><a id="nope₂"></a><a id="41598" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#41598" class="Function">nope₂</a> <a id="41604" class="Symbol">:</a> <a id="41606" class="Symbol">∀</a> <a id="41608" class="Symbol">{</a><a id="41609" href="plfa.part2.Lambda.html#41609" class="Bound">A</a><a id="41610" class="Symbol">}</a> <a id="41612" class="Symbol">→</a> <a id="41614" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#535" class="Function Operator">¬</a> <a id="41616" class="Symbol">(</a><a id="41617" href="plfa.part2.Lambda.html#31092" class="InductiveConstructor">∅</a> <a id="41619" href="plfa.part2.Lambda.html#33468" class="Datatype Operator">⊢</a> <a id="41621" href="plfa.part2.Lambda.html#3812" class="InductiveConstructor Operator">ƛ</a> <a id="41623" class="String">&quot;x&quot;</a> <a id="41627" href="plfa.part2.Lambda.html#3812" class="InductiveConstructor Operator">⇒</a> <a id="41629" href="plfa.part2.Lambda.html#3773" class="InductiveConstructor Operator">`</a> <a id="41631" class="String">&quot;x&quot;</a> <a id="41635" href="plfa.part2.Lambda.html#3858" class="InductiveConstructor Operator">·</a> <a id="41637" href="plfa.part2.Lambda.html#3773" class="InductiveConstructor Operator">`</a> <a id="41639" class="String">&quot;x&quot;</a> <a id="41643" href="plfa.part2.Lambda.html#33468" class="Datatype Operator">⦂</a> <a id="41645" href="plfa.part2.Lambda.html#41609" class="Bound">A</a><a id="41646" class="Symbol">)</a>
<a id="41648" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#41598" class="Function">nope₂</a> <a id="41654" class="Symbol">(</a><a id="41655" href="plfa.part2.Lambda.html#33603" class="InductiveConstructor">⊢ƛ</a> <a id="41658" class="Symbol">(</a><a id="41659" href="plfa.part2.Lambda.html#33524" class="InductiveConstructor">⊢`</a> <a id="41662" href="plfa.part2.Lambda.html#41662" class="Bound">∋x</a> <a id="41665" href="plfa.part2.Lambda.html#33710" class="InductiveConstructor Operator">·</a> <a id="41667" href="plfa.part2.Lambda.html#33524" class="InductiveConstructor">⊢`</a> <a id="41670" href="plfa.part2.Lambda.html#41670" class="Bound">∋x′</a><a id="41673" class="Symbol">))</a>  <a id="41677" class="Symbol">=</a>  <a id="41680" href="plfa.part2.Lambda.html#41725" class="Function">contradiction</a> <a id="41694" class="Symbol">(</a><a id="41695" href="plfa.part2.Lambda.html#40645" class="Function">∋-injective</a> <a id="41707" href="plfa.part2.Lambda.html#41662" class="Bound">∋x</a> <a id="41710" href="plfa.part2.Lambda.html#41670" class="Bound">∋x′</a><a id="41713" class="Symbol">)</a>
  <a id="41717" class="Keyword">where</a>
  <a id="41725" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#41725" class="Function">contradiction</a> <a id="41739" class="Symbol">:</a> <a id="41741" class="Symbol">∀</a> <a id="41743" class="Symbol">{</a><a id="41744" href="plfa.part2.Lambda.html#41744" class="Bound">A</a> <a id="41746" href="plfa.part2.Lambda.html#41746" class="Bound">B</a><a id="41747" class="Symbol">}</a> <a id="41749" class="Symbol">→</a> <a id="41751" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#535" class="Function Operator">¬</a> <a id="41753" class="Symbol">(</a><a id="41754" href="plfa.part2.Lambda.html#41744" class="Bound">A</a> <a id="41756" href="plfa.part2.Lambda.html#29431" class="InductiveConstructor Operator">⇒</a> <a id="41758" href="plfa.part2.Lambda.html#41746" class="Bound">B</a> <a id="41760" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="41762" href="plfa.part2.Lambda.html#41744" class="Bound">A</a><a id="41763" class="Symbol">)</a>
  <a id="41767" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#41725" class="Function">contradiction</a> <a id="41781" class="Symbol">()</a>
</pre>{% endraw %}

#### Quiz

For each of the following, give a type `A` for which it is derivable,
or explain why there is no such `A`.

1. `` ∅ , "y" ⦂ `ℕ ⇒ `ℕ , "x" ⦂ `ℕ ⊢ ` "y" · ` "x" ⦂ A ``
2. `` ∅ , "y" ⦂ `ℕ ⇒ `ℕ , "x" ⦂ `ℕ ⊢ ` "x" · ` "y" ⦂ A ``
3. `` ∅ , "y" ⦂ `ℕ ⇒ `ℕ ⊢ ƛ "x" ⇒ ` "y" · ` "x" ⦂ A ``

For each of the following, give types `A`, `B`, and `C` for which it is derivable,
or explain why there are no such types.

1. `` ∅ , "x" ⦂ A ⊢ ` "x" · ` "x" ⦂ B ``
2. `` ∅ , "x" ⦂ A , "y" ⦂ B ⊢ ƛ "z" ⇒ ` "x" · (` "y" · ` "z") ⦂ C ``


#### Exercise `mul-type` (recommended)

Using the term `mul` you defined earlier, write out the derivation
showing that it is well typed.

{% raw %}<pre class="Agda"><a id="42460" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}

#### Exercise `mulᶜ-type` (practice)

Using the term `mulᶜ` you defined earlier, write out the derivation
showing that it is well typed.

{% raw %}<pre class="Agda"><a id="42631" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}

## Unicode

This chapter uses the following unicode:

    ⇒  U+21D2  RIGHTWARDS DOUBLE ARROW (\=>)
    ƛ  U+019B  LATIN SMALL LETTER LAMBDA WITH STROKE (\Gl-)
    ·  U+00B7  MIDDLE DOT (\cdot)
    —  U+2014  EM DASH (\em)
    ↠  U+21A0  RIGHTWARDS TWO HEADED ARROW (\rr-)
    ξ  U+03BE  GREEK SMALL LETTER XI (\Gx or \xi)
    β  U+03B2  GREEK SMALL LETTER BETA (\Gb or \beta)
    Γ  U+0393  GREEK CAPITAL LETTER GAMMA (\GG or \Gamma)
    ≠  U+2260  NOT EQUAL TO (\=n or \ne)
    ∋  U+220B  CONTAINS AS MEMBER (\ni)
    ∅  U+2205  EMPTY SET (\0)
    ⊢  U+22A2  RIGHT TACK (\vdash or \|-)
    ⦂  U+2982  Z NOTATION TYPE COLON (\:)
    😇  U+1F607  SMILING FACE WITH HALO
    😈  U+1F608  SMILING FACE WITH HORNS

We compose reduction `—→` from an em dash `—` and an arrow `→`.
Similarly for reflexive and transitive closure `—↠`.
