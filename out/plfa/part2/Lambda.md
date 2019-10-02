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
intrinsically-typed terms, as we will do in
Chapter [DeBruijn]({{ site.baseurl }}/DeBruijn/),
leads to a more compact formulation.  Nonetheless, we begin with named
variables and extrinsically-typed terms,
partly because names are easier than indices to read,
and partly because the development is more traditional.

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

{% raw %}<pre class="Agda"><a id="2304" class="Keyword">open</a> <a id="2309" class="Keyword">import</a> <a id="2316" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.html" class="Module">Relation.Binary.PropositionalEquality</a> <a id="2354" class="Keyword">using</a> <a id="2360" class="Symbol">(</a><a id="2361" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">_≡_</a><a id="2364" class="Symbol">;</a> <a id="2366" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#799" class="Function Operator">_≢_</a><a id="2369" class="Symbol">;</a> <a id="2371" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a><a id="2375" class="Symbol">)</a>
<a id="2377" class="Keyword">open</a> <a id="2382" class="Keyword">import</a> <a id="2389" href="https://agda.github.io/agda-stdlib/v1.1/Data.String.html" class="Module">Data.String</a> <a id="2401" class="Keyword">using</a> <a id="2407" class="Symbol">(</a><a id="2408" href="Agda.Builtin.String.html#206" class="Postulate">String</a><a id="2414" class="Symbol">;</a> <a id="2416" href="https://agda.github.io/agda-stdlib/v1.1/Data.String.Properties.html#2569" class="Function Operator">_≟_</a><a id="2419" class="Symbol">)</a>
<a id="2421" class="Keyword">open</a> <a id="2426" class="Keyword">import</a> <a id="2433" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.html" class="Module">Data.Nat</a> <a id="2442" class="Keyword">using</a> <a id="2448" class="Symbol">(</a><a id="2449" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="2450" class="Symbol">;</a> <a id="2452" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a><a id="2456" class="Symbol">;</a> <a id="2458" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a><a id="2461" class="Symbol">)</a>
<a id="2463" class="Keyword">open</a> <a id="2468" class="Keyword">import</a> <a id="2475" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html" class="Module">Data.Empty</a> <a id="2486" class="Keyword">using</a> <a id="2492" class="Symbol">(</a><a id="2493" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html#279" class="Datatype">⊥</a><a id="2494" class="Symbol">;</a> <a id="2496" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html#294" class="Function">⊥-elim</a><a id="2502" class="Symbol">)</a>
<a id="2504" class="Keyword">open</a> <a id="2509" class="Keyword">import</a> <a id="2516" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html" class="Module">Relation.Nullary</a> <a id="2533" class="Keyword">using</a> <a id="2539" class="Symbol">(</a><a id="2540" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#605" class="Datatype">Dec</a><a id="2543" class="Symbol">;</a> <a id="2545" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#641" class="InductiveConstructor">yes</a><a id="2548" class="Symbol">;</a> <a id="2550" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#668" class="InductiveConstructor">no</a><a id="2552" class="Symbol">;</a> <a id="2554" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#535" class="Function Operator">¬_</a><a id="2556" class="Symbol">)</a>
<a id="2558" class="Keyword">open</a> <a id="2563" class="Keyword">import</a> <a id="2570" href="https://agda.github.io/agda-stdlib/v1.1/Data.List.html" class="Module">Data.List</a> <a id="2580" class="Keyword">using</a> <a id="2586" class="Symbol">(</a><a id="2587" href="Agda.Builtin.List.html#121" class="Datatype">List</a><a id="2591" class="Symbol">;</a> <a id="2593" href="Agda.Builtin.List.html#173" class="InductiveConstructor Operator">_∷_</a><a id="2596" class="Symbol">;</a> <a id="2598" href="https://agda.github.io/agda-stdlib/v1.1/Data.List.Base.html#8786" class="InductiveConstructor">[]</a><a id="2600" class="Symbol">)</a>
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
{% raw %}<pre class="Agda"><a id="Id"></a><a id="3695" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3695" class="Function">Id</a> <a id="3698" class="Symbol">:</a> <a id="3700" class="PrimitiveType">Set</a>
<a id="3704" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3695" class="Function">Id</a> <a id="3707" class="Symbol">=</a> <a id="3709" href="Agda.Builtin.String.html#206" class="Postulate">String</a>

<a id="3717" class="Keyword">infix</a>  <a id="3724" class="Number">5</a>  <a id="3727" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3854" class="InductiveConstructor Operator">ƛ_⇒_</a>
<a id="3732" class="Keyword">infix</a>  <a id="3739" class="Number">5</a>  <a id="3742" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#4083" class="InductiveConstructor Operator">μ_⇒_</a>
<a id="3747" class="Keyword">infixl</a> <a id="3754" class="Number">7</a>  <a id="3757" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#34330" class="InductiveConstructor Operator">_·_</a>
<a id="3761" class="Keyword">infix</a>  <a id="3768" class="Number">8</a>  <a id="3771" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3982" class="InductiveConstructor Operator">`suc_</a>
<a id="3777" class="Keyword">infix</a>  <a id="3784" class="Number">9</a>  <a id="3787" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3815" class="InductiveConstructor Operator">`_</a>

<a id="3791" class="Keyword">data</a> <a id="Term"></a><a id="3796" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3796" class="Datatype">Term</a> <a id="3801" class="Symbol">:</a> <a id="3803" class="PrimitiveType">Set</a> <a id="3807" class="Keyword">where</a>
  <a id="Term.`_"></a><a id="3815" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3815" class="InductiveConstructor Operator">`_</a>                      <a id="3839" class="Symbol">:</a>  <a id="3842" href="plfa.part2.Lambda.html#3695" class="Function">Id</a> <a id="3845" class="Symbol">→</a> <a id="3847" href="plfa.part2.Lambda.html#3796" class="Datatype">Term</a>
  <a id="Term.ƛ_⇒_"></a><a id="3854" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3854" class="InductiveConstructor Operator">ƛ_⇒_</a>                    <a id="3878" class="Symbol">:</a>  <a id="3881" href="plfa.part2.Lambda.html#3695" class="Function">Id</a> <a id="3884" class="Symbol">→</a> <a id="3886" href="plfa.part2.Lambda.html#3796" class="Datatype">Term</a> <a id="3891" class="Symbol">→</a> <a id="3893" href="plfa.part2.Lambda.html#3796" class="Datatype">Term</a>
  <a id="Term._·_"></a><a id="3900" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3900" class="InductiveConstructor Operator">_·_</a>                     <a id="3924" class="Symbol">:</a>  <a id="3927" href="plfa.part2.Lambda.html#3796" class="Datatype">Term</a> <a id="3932" class="Symbol">→</a> <a id="3934" href="plfa.part2.Lambda.html#3796" class="Datatype">Term</a> <a id="3939" class="Symbol">→</a> <a id="3941" href="plfa.part2.Lambda.html#3796" class="Datatype">Term</a>
  <a id="Term.`zero"></a><a id="3948" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3948" class="InductiveConstructor">`zero</a>                   <a id="3972" class="Symbol">:</a>  <a id="3975" href="plfa.part2.Lambda.html#3796" class="Datatype">Term</a>
  <a id="Term.`suc_"></a><a id="3982" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3982" class="InductiveConstructor Operator">`suc_</a>                   <a id="4006" class="Symbol">:</a>  <a id="4009" href="plfa.part2.Lambda.html#3796" class="Datatype">Term</a> <a id="4014" class="Symbol">→</a> <a id="4016" href="plfa.part2.Lambda.html#3796" class="Datatype">Term</a>
  <a id="Term.case_[zero⇒_|suc_⇒_]"></a><a id="4023" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#4023" class="InductiveConstructor Operator">case_[zero⇒_|suc_⇒_]</a>    <a id="4047" class="Symbol">:</a>  <a id="4050" href="plfa.part2.Lambda.html#3796" class="Datatype">Term</a> <a id="4055" class="Symbol">→</a> <a id="4057" href="plfa.part2.Lambda.html#3796" class="Datatype">Term</a> <a id="4062" class="Symbol">→</a> <a id="4064" href="plfa.part2.Lambda.html#3695" class="Function">Id</a> <a id="4067" class="Symbol">→</a> <a id="4069" href="plfa.part2.Lambda.html#3796" class="Datatype">Term</a> <a id="4074" class="Symbol">→</a> <a id="4076" href="plfa.part2.Lambda.html#3796" class="Datatype">Term</a>
  <a id="Term.μ_⇒_"></a><a id="4083" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#4083" class="InductiveConstructor Operator">μ_⇒_</a>                    <a id="4107" class="Symbol">:</a>  <a id="4110" href="plfa.part2.Lambda.html#3695" class="Function">Id</a> <a id="4113" class="Symbol">→</a> <a id="4115" href="plfa.part2.Lambda.html#3796" class="Datatype">Term</a> <a id="4120" class="Symbol">→</a> <a id="4122" href="plfa.part2.Lambda.html#3796" class="Datatype">Term</a>
</pre>{% endraw %}We represent identifiers by strings.  We choose precedence so that
lambda abstraction and fixpoint bind least tightly, then application,
then successor, and tightest of all is the constructor for variables.
Case expressions are self-bracketing.


### Example terms

Here are some example terms: the natural number two,
a function that adds naturals,
and a term that computes two plus two:
{% raw %}<pre class="Agda"><a id="two"></a><a id="4524" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#4524" class="Function">two</a> <a id="4528" class="Symbol">:</a> <a id="4530" href="plfa.part2.Lambda.html#3796" class="Datatype">Term</a>
<a id="4535" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#4524" class="Function">two</a> <a id="4539" class="Symbol">=</a> <a id="4541" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="4546" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="4551" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a>

<a id="plus"></a><a id="4558" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#4558" class="Function">plus</a> <a id="4563" class="Symbol">:</a> <a id="4565" href="plfa.part2.Lambda.html#3796" class="Datatype">Term</a>
<a id="4570" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#4558" class="Function">plus</a> <a id="4575" class="Symbol">=</a> <a id="4577" href="plfa.part2.Lambda.html#4083" class="InductiveConstructor Operator">μ</a> <a id="4579" class="String">&quot;+&quot;</a> <a id="4583" href="plfa.part2.Lambda.html#4083" class="InductiveConstructor Operator">⇒</a> <a id="4585" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">ƛ</a> <a id="4587" class="String">&quot;m&quot;</a> <a id="4591" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a> <a id="4593" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">ƛ</a> <a id="4595" class="String">&quot;n&quot;</a> <a id="4599" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a>
         <a id="4610" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#4023" class="InductiveConstructor Operator">case</a> <a id="4615" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="4617" class="String">&quot;m&quot;</a>
           <a id="4632" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#4023" class="InductiveConstructor Operator">[zero⇒</a> <a id="4639" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="4641" class="String">&quot;n&quot;</a>
           <a id="4656" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#4023" class="InductiveConstructor Operator">|suc</a> <a id="4661" class="String">&quot;m&quot;</a> <a id="4665" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">⇒</a> <a id="4667" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="4672" class="Symbol">(</a><a id="4673" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="4675" class="String">&quot;+&quot;</a> <a id="4679" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="4681" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="4683" class="String">&quot;m&quot;</a> <a id="4687" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="4689" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="4691" class="String">&quot;n&quot;</a><a id="4694" class="Symbol">)</a> <a id="4696" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">]</a>
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
{% raw %}<pre class="Agda"><a id="twoᶜ"></a><a id="5773" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#5773" class="Function">twoᶜ</a> <a id="5778" class="Symbol">:</a> <a id="5780" href="plfa.part2.Lambda.html#3796" class="Datatype">Term</a>
<a id="5785" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#5773" class="Function">twoᶜ</a> <a id="5790" class="Symbol">=</a>  <a id="5793" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">ƛ</a> <a id="5795" class="String">&quot;s&quot;</a> <a id="5799" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a> <a id="5801" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">ƛ</a> <a id="5803" class="String">&quot;z&quot;</a> <a id="5807" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a> <a id="5809" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="5811" class="String">&quot;s&quot;</a> <a id="5815" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="5817" class="Symbol">(</a><a id="5818" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="5820" class="String">&quot;s&quot;</a> <a id="5824" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="5826" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="5828" class="String">&quot;z&quot;</a><a id="5831" class="Symbol">)</a>

<a id="plusᶜ"></a><a id="5834" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#5834" class="Function">plusᶜ</a> <a id="5840" class="Symbol">:</a> <a id="5842" href="plfa.part2.Lambda.html#3796" class="Datatype">Term</a>
<a id="5847" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#5834" class="Function">plusᶜ</a> <a id="5853" class="Symbol">=</a>  <a id="5856" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">ƛ</a> <a id="5858" class="String">&quot;m&quot;</a> <a id="5862" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a> <a id="5864" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">ƛ</a> <a id="5866" class="String">&quot;n&quot;</a> <a id="5870" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a> <a id="5872" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">ƛ</a> <a id="5874" class="String">&quot;s&quot;</a> <a id="5878" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a> <a id="5880" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">ƛ</a> <a id="5882" class="String">&quot;z&quot;</a> <a id="5886" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a>
         <a id="5897" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3815" class="InductiveConstructor Operator">`</a> <a id="5899" class="String">&quot;m&quot;</a> <a id="5903" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="5905" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="5907" class="String">&quot;s&quot;</a> <a id="5911" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="5913" class="Symbol">(</a><a id="5914" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="5916" class="String">&quot;n&quot;</a> <a id="5920" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="5922" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="5924" class="String">&quot;s&quot;</a> <a id="5928" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="5930" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="5932" class="String">&quot;z&quot;</a><a id="5935" class="Symbol">)</a>

<a id="sucᶜ"></a><a id="5938" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#5938" class="Function">sucᶜ</a> <a id="5943" class="Symbol">:</a> <a id="5945" href="plfa.part2.Lambda.html#3796" class="Datatype">Term</a>
<a id="5950" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#5938" class="Function">sucᶜ</a> <a id="5955" class="Symbol">=</a> <a id="5957" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">ƛ</a> <a id="5959" class="String">&quot;n&quot;</a> <a id="5963" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a> <a id="5965" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="5970" class="Symbol">(</a><a id="5971" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="5973" class="String">&quot;n&quot;</a><a id="5976" class="Symbol">)</a>
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

{% raw %}<pre class="Agda"><a id="6858" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}

#### Exercise `mulᶜ` (practice)

Write out the definition of a lambda term that multiplies
two natural numbers represented as Church numerals. Your
definition may use `plusᶜ` as defined earlier (or may not
— there are nice definitions both ways).

{% raw %}<pre class="Agda"><a id="7139" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}

#### Exercise `primed` (stretch) {#primed}

Some people find it annoying to write `` ` "x" `` instead of `x`.
We can make examples with lambda terms slightly easier to write
by adding the following definitions:
{% raw %}<pre class="Agda"><a id="ƛ′_⇒_"></a><a id="7383" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#7383" class="Function Operator">ƛ′_⇒_</a> <a id="7389" class="Symbol">:</a> <a id="7391" href="plfa.part2.Lambda.html#3796" class="Datatype">Term</a> <a id="7396" class="Symbol">→</a> <a id="7398" href="plfa.part2.Lambda.html#3796" class="Datatype">Term</a> <a id="7403" class="Symbol">→</a> <a id="7405" href="plfa.part2.Lambda.html#3796" class="Datatype">Term</a>
<a id="7410" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#7383" class="Function Operator">ƛ′</a> <a id="7413" class="Symbol">(</a><a id="7414" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="7416" href="plfa.part2.Lambda.html#7416" class="Bound">x</a><a id="7417" class="Symbol">)</a> <a id="7419" href="plfa.part2.Lambda.html#7383" class="Function Operator">⇒</a> <a id="7421" href="plfa.part2.Lambda.html#7421" class="Bound">N</a>  <a id="7424" class="Symbol">=</a>  <a id="7427" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">ƛ</a> <a id="7429" href="plfa.part2.Lambda.html#7416" class="Bound">x</a> <a id="7431" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a> <a id="7433" href="plfa.part2.Lambda.html#7421" class="Bound">N</a>
<a id="7435" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#7383" class="CatchallClause Function Operator">ƛ′</a><a id="7437" class="CatchallClause"> </a><a id="7438" class="CatchallClause Symbol">_</a><a id="7439" class="CatchallClause"> </a><a id="7440" href="plfa.part2.Lambda.html#7383" class="CatchallClause Function Operator">⇒</a><a id="7441" class="CatchallClause"> </a><a id="7442" class="CatchallClause Symbol">_</a>      <a id="7449" class="Symbol">=</a>  <a id="7452" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html#294" class="Function">⊥-elim</a> <a id="7459" href="plfa.part2.Lambda.html#7488" class="Postulate">impossible</a>
  <a id="7472" class="Keyword">where</a> <a id="7478" class="Keyword">postulate</a> <a id="7488" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#7488" class="Postulate">impossible</a> <a id="7499" class="Symbol">:</a> <a id="7501" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html#279" class="Datatype">⊥</a>

<a id="case′_[zero⇒_|suc_⇒_]"></a><a id="7504" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#7504" class="Function Operator">case′_[zero⇒_|suc_⇒_]</a> <a id="7526" class="Symbol">:</a> <a id="7528" href="plfa.part2.Lambda.html#3796" class="Datatype">Term</a> <a id="7533" class="Symbol">→</a> <a id="7535" href="plfa.part2.Lambda.html#3796" class="Datatype">Term</a> <a id="7540" class="Symbol">→</a> <a id="7542" href="plfa.part2.Lambda.html#3796" class="Datatype">Term</a> <a id="7547" class="Symbol">→</a> <a id="7549" href="plfa.part2.Lambda.html#3796" class="Datatype">Term</a> <a id="7554" class="Symbol">→</a> <a id="7556" href="plfa.part2.Lambda.html#3796" class="Datatype">Term</a>
<a id="7561" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#7504" class="Function Operator">case′</a> <a id="7567" href="plfa.part2.Lambda.html#7567" class="Bound">L</a> <a id="7569" href="plfa.part2.Lambda.html#7504" class="Function Operator">[zero⇒</a> <a id="7576" href="plfa.part2.Lambda.html#7576" class="Bound">M</a> <a id="7578" href="plfa.part2.Lambda.html#7504" class="Function Operator">|suc</a> <a id="7583" class="Symbol">(</a><a id="7584" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="7586" href="plfa.part2.Lambda.html#7586" class="Bound">x</a><a id="7587" class="Symbol">)</a> <a id="7589" href="plfa.part2.Lambda.html#7504" class="Function Operator">⇒</a> <a id="7591" href="plfa.part2.Lambda.html#7591" class="Bound">N</a> <a id="7593" href="plfa.part2.Lambda.html#7504" class="Function Operator">]</a>  <a id="7596" class="Symbol">=</a>  <a id="7599" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">case</a> <a id="7604" href="plfa.part2.Lambda.html#7567" class="Bound">L</a> <a id="7606" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">[zero⇒</a> <a id="7613" href="plfa.part2.Lambda.html#7576" class="Bound">M</a> <a id="7615" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">|suc</a> <a id="7620" href="plfa.part2.Lambda.html#7586" class="Bound">x</a> <a id="7622" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">⇒</a> <a id="7624" href="plfa.part2.Lambda.html#7591" class="Bound">N</a> <a id="7626" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">]</a>
<a id="7628" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#7504" class="CatchallClause Function Operator">case′</a><a id="7633" class="CatchallClause"> </a><a id="7634" class="CatchallClause Symbol">_</a><a id="7635" class="CatchallClause"> </a><a id="7636" href="plfa.part2.Lambda.html#7504" class="CatchallClause Function Operator">[zero⇒</a><a id="7642" class="CatchallClause"> </a><a id="7643" class="CatchallClause Symbol">_</a><a id="7644" class="CatchallClause"> </a><a id="7645" href="plfa.part2.Lambda.html#7504" class="CatchallClause Function Operator">|suc</a><a id="7649" class="CatchallClause"> </a><a id="7650" class="CatchallClause Symbol">_</a><a id="7651" class="CatchallClause"> </a><a id="7652" href="plfa.part2.Lambda.html#7504" class="CatchallClause Function Operator">⇒</a><a id="7653" class="CatchallClause"> </a><a id="7654" class="CatchallClause Symbol">_</a><a id="7655" class="CatchallClause"> </a><a id="7656" href="plfa.part2.Lambda.html#7504" class="CatchallClause Function Operator">]</a>      <a id="7663" class="Symbol">=</a>  <a id="7666" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html#294" class="Function">⊥-elim</a> <a id="7673" href="plfa.part2.Lambda.html#7702" class="Postulate">impossible</a>
  <a id="7686" class="Keyword">where</a> <a id="7692" class="Keyword">postulate</a> <a id="7702" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#7702" class="Postulate">impossible</a> <a id="7713" class="Symbol">:</a> <a id="7715" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html#279" class="Datatype">⊥</a>

<a id="μ′_⇒_"></a><a id="7718" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#7718" class="Function Operator">μ′_⇒_</a> <a id="7724" class="Symbol">:</a> <a id="7726" href="plfa.part2.Lambda.html#3796" class="Datatype">Term</a> <a id="7731" class="Symbol">→</a> <a id="7733" href="plfa.part2.Lambda.html#3796" class="Datatype">Term</a> <a id="7738" class="Symbol">→</a> <a id="7740" href="plfa.part2.Lambda.html#3796" class="Datatype">Term</a>
<a id="7745" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#7718" class="Function Operator">μ′</a> <a id="7748" class="Symbol">(</a><a id="7749" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="7751" href="plfa.part2.Lambda.html#7751" class="Bound">x</a><a id="7752" class="Symbol">)</a> <a id="7754" href="plfa.part2.Lambda.html#7718" class="Function Operator">⇒</a> <a id="7756" href="plfa.part2.Lambda.html#7756" class="Bound">N</a>  <a id="7759" class="Symbol">=</a>  <a id="7762" href="plfa.part2.Lambda.html#4083" class="InductiveConstructor Operator">μ</a> <a id="7764" href="plfa.part2.Lambda.html#7751" class="Bound">x</a> <a id="7766" href="plfa.part2.Lambda.html#4083" class="InductiveConstructor Operator">⇒</a> <a id="7768" href="plfa.part2.Lambda.html#7756" class="Bound">N</a>
<a id="7770" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#7718" class="CatchallClause Function Operator">μ′</a><a id="7772" class="CatchallClause"> </a><a id="7773" class="CatchallClause Symbol">_</a><a id="7774" class="CatchallClause"> </a><a id="7775" href="plfa.part2.Lambda.html#7718" class="CatchallClause Function Operator">⇒</a><a id="7776" class="CatchallClause"> </a><a id="7777" class="CatchallClause Symbol">_</a>      <a id="7784" class="Symbol">=</a>  <a id="7787" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html#294" class="Function">⊥-elim</a> <a id="7794" href="plfa.part2.Lambda.html#7823" class="Postulate">impossible</a>
  <a id="7807" class="Keyword">where</a> <a id="7813" class="Keyword">postulate</a> <a id="7823" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#7823" class="Postulate">impossible</a> <a id="7834" class="Symbol">:</a> <a id="7836" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html#279" class="Datatype">⊥</a>
</pre>{% endraw %}We intend to apply the function only when the first term is a variable, which we
indicate by postulating a term `impossible` of the empty type `⊥`.  If we use
C-c C-n to normalise the term

  ƛ′ two ⇒ two

Agda will return an answer warning us that the impossible has occurred:

  ⊥-elim (plfa.part2.Lambda.impossible (`` `suc (`suc `zero)) (`suc (`suc `zero)) ``)

While postulating the impossible is a useful technique, it must be
used with care, since such postulation could allow us to provide
evidence of _any_ proposition whatsoever, regardless of its truth.

The definition of `plus` can now be written as follows:
{% raw %}<pre class="Agda"><a id="plus′"></a><a id="8468" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#8468" class="Function">plus′</a> <a id="8474" class="Symbol">:</a> <a id="8476" href="plfa.part2.Lambda.html#3796" class="Datatype">Term</a>
<a id="8481" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#8468" class="Function">plus′</a> <a id="8487" class="Symbol">=</a> <a id="8489" href="plfa.part2.Lambda.html#7718" class="Function Operator">μ′</a> <a id="8492" href="plfa.part2.Lambda.html#8599" class="Function">+</a> <a id="8494" href="plfa.part2.Lambda.html#7718" class="Function Operator">⇒</a> <a id="8496" href="plfa.part2.Lambda.html#7383" class="Function Operator">ƛ′</a> <a id="8499" href="plfa.part2.Lambda.html#8613" class="Function">m</a> <a id="8501" href="plfa.part2.Lambda.html#7383" class="Function Operator">⇒</a> <a id="8503" href="plfa.part2.Lambda.html#7383" class="Function Operator">ƛ′</a> <a id="8506" href="plfa.part2.Lambda.html#8627" class="Function">n</a> <a id="8508" href="plfa.part2.Lambda.html#7383" class="Function Operator">⇒</a>
          <a id="8520" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#7504" class="Function Operator">case′</a> <a id="8526" href="plfa.part2.Lambda.html#8613" class="Function">m</a>
            <a id="8540" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#7504" class="Function Operator">[zero⇒</a> <a id="8547" href="plfa.part2.Lambda.html#8627" class="Function">n</a>
            <a id="8561" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#7504" class="Function Operator">|suc</a> <a id="8566" href="plfa.part2.Lambda.html#8613" class="Function">m</a> <a id="8568" href="plfa.part2.Lambda.html#7504" class="Function Operator">⇒</a> <a id="8570" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="8575" class="Symbol">(</a><a id="8576" href="plfa.part2.Lambda.html#8599" class="Function">+</a> <a id="8578" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="8580" href="plfa.part2.Lambda.html#8613" class="Function">m</a> <a id="8582" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="8584" href="plfa.part2.Lambda.html#8627" class="Function">n</a><a id="8585" class="Symbol">)</a> <a id="8587" href="plfa.part2.Lambda.html#7504" class="Function Operator">]</a>
  <a id="8591" class="Keyword">where</a>
  <a id="8599" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#8599" class="Function">+</a>  <a id="8602" class="Symbol">=</a>  <a id="8605" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="8607" class="String">&quot;+&quot;</a>
  <a id="8613" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#8613" class="Function">m</a>  <a id="8616" class="Symbol">=</a>  <a id="8619" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="8621" class="String">&quot;m&quot;</a>
  <a id="8627" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#8627" class="Function">n</a>  <a id="8630" class="Symbol">=</a>  <a id="8633" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="8635" class="String">&quot;n&quot;</a>
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

{% raw %}<pre class="Agda"><a id="12166" class="Keyword">data</a> <a id="Value"></a><a id="12171" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#12171" class="Datatype">Value</a> <a id="12177" class="Symbol">:</a> <a id="12179" href="plfa.part2.Lambda.html#3796" class="Datatype">Term</a> <a id="12184" class="Symbol">→</a> <a id="12186" class="PrimitiveType">Set</a> <a id="12190" class="Keyword">where</a>

  <a id="Value.V-ƛ"></a><a id="12199" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#12199" class="InductiveConstructor">V-ƛ</a> <a id="12203" class="Symbol">:</a> <a id="12205" class="Symbol">∀</a> <a id="12207" class="Symbol">{</a><a id="12208" href="plfa.part2.Lambda.html#12208" class="Bound">x</a> <a id="12210" href="plfa.part2.Lambda.html#12210" class="Bound">N</a><a id="12211" class="Symbol">}</a>
      <a id="12219" class="Comment">---------------</a>
    <a id="12239" class="Symbol">→</a> <a id="12241" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#12171" class="Datatype">Value</a> <a id="12247" class="Symbol">(</a><a id="12248" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">ƛ</a> <a id="12250" href="plfa.part2.Lambda.html#12208" class="Bound">x</a> <a id="12252" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a> <a id="12254" href="plfa.part2.Lambda.html#12210" class="Bound">N</a><a id="12255" class="Symbol">)</a>

  <a id="Value.V-zero"></a><a id="12260" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#12260" class="InductiveConstructor">V-zero</a> <a id="12267" class="Symbol">:</a>
      <a id="12275" class="Comment">-----------</a>
      <a id="12293" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#12171" class="Datatype">Value</a> <a id="12299" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a>

  <a id="Value.V-suc"></a><a id="12308" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#12308" class="InductiveConstructor">V-suc</a> <a id="12314" class="Symbol">:</a> <a id="12316" class="Symbol">∀</a> <a id="12318" class="Symbol">{</a><a id="12319" href="plfa.part2.Lambda.html#12319" class="Bound">V</a><a id="12320" class="Symbol">}</a>
    <a id="12326" class="Symbol">→</a> <a id="12328" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#12171" class="Datatype">Value</a> <a id="12334" href="plfa.part2.Lambda.html#12319" class="Bound">V</a>
      <a id="12342" class="Comment">--------------</a>
    <a id="12361" class="Symbol">→</a> <a id="12363" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#12171" class="Datatype">Value</a> <a id="12369" class="Symbol">(</a><a id="12370" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="12375" href="plfa.part2.Lambda.html#12319" class="Bound">V</a><a id="12376" class="Symbol">)</a>
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

{% raw %}<pre class="Agda"><a id="15537" class="Keyword">infix</a> <a id="15543" class="Number">9</a> <a id="15545" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#15554" class="Function Operator">_[_:=_]</a>

<a id="_[_:=_]"></a><a id="15554" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#15554" class="Function Operator">_[_:=_]</a> <a id="15562" class="Symbol">:</a> <a id="15564" href="plfa.part2.Lambda.html#3796" class="Datatype">Term</a> <a id="15569" class="Symbol">→</a> <a id="15571" href="plfa.part2.Lambda.html#3695" class="Function">Id</a> <a id="15574" class="Symbol">→</a> <a id="15576" href="plfa.part2.Lambda.html#3796" class="Datatype">Term</a> <a id="15581" class="Symbol">→</a> <a id="15583" href="plfa.part2.Lambda.html#3796" class="Datatype">Term</a>
<a id="15588" class="Symbol">(</a><a id="15589" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3815" class="InductiveConstructor Operator">`</a> <a id="15591" href="plfa.part2.Lambda.html#15591" class="Bound">x</a><a id="15592" class="Symbol">)</a> <a id="15594" href="plfa.part2.Lambda.html#15554" class="Function Operator">[</a> <a id="15596" href="plfa.part2.Lambda.html#15596" class="Bound">y</a> <a id="15598" href="plfa.part2.Lambda.html#15554" class="Function Operator">:=</a> <a id="15601" href="plfa.part2.Lambda.html#15601" class="Bound">V</a> <a id="15603" href="plfa.part2.Lambda.html#15554" class="Function Operator">]</a> <a id="15605" class="Keyword">with</a> <a id="15610" href="plfa.part2.Lambda.html#15591" class="Bound">x</a> <a id="15612" href="https://agda.github.io/agda-stdlib/v1.1/Data.String.Properties.html#2569" class="Function Operator">≟</a> <a id="15614" href="plfa.part2.Lambda.html#15596" class="Bound">y</a>
<a id="15616" class="Symbol">...</a> <a id="15620" class="Symbol">|</a> <a id="15622" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#641" class="InductiveConstructor">yes</a> <a id="15626" class="Symbol">_</a>          <a id="15637" class="Symbol">=</a>  <a id="15640" class="Bound">V</a>
<a id="15642" class="Symbol">...</a> <a id="15646" class="Symbol">|</a> <a id="15648" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#668" class="InductiveConstructor">no</a>  <a id="15652" class="Symbol">_</a>          <a id="15663" class="Symbol">=</a>  <a id="15666" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3815" class="InductiveConstructor Operator">`</a> <a id="15668" class="Bound">x</a>
<a id="15670" class="Symbol">(</a><a id="15671" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3854" class="InductiveConstructor Operator">ƛ</a> <a id="15673" href="plfa.part2.Lambda.html#15673" class="Bound">x</a> <a id="15675" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a> <a id="15677" href="plfa.part2.Lambda.html#15677" class="Bound">N</a><a id="15678" class="Symbol">)</a> <a id="15680" href="plfa.part2.Lambda.html#15554" class="Function Operator">[</a> <a id="15682" href="plfa.part2.Lambda.html#15682" class="Bound">y</a> <a id="15684" href="plfa.part2.Lambda.html#15554" class="Function Operator">:=</a> <a id="15687" href="plfa.part2.Lambda.html#15687" class="Bound">V</a> <a id="15689" href="plfa.part2.Lambda.html#15554" class="Function Operator">]</a> <a id="15691" class="Keyword">with</a> <a id="15696" href="plfa.part2.Lambda.html#15673" class="Bound">x</a> <a id="15698" href="https://agda.github.io/agda-stdlib/v1.1/Data.String.Properties.html#2569" class="Function Operator">≟</a> <a id="15700" href="plfa.part2.Lambda.html#15682" class="Bound">y</a>
<a id="15702" class="Symbol">...</a> <a id="15706" class="Symbol">|</a> <a id="15708" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#641" class="InductiveConstructor">yes</a> <a id="15712" class="Symbol">_</a>          <a id="15723" class="Symbol">=</a>  <a id="15726" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3854" class="InductiveConstructor Operator">ƛ</a> <a id="15728" class="Bound">x</a> <a id="15730" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a> <a id="15732" class="Bound">N</a>
<a id="15734" class="Symbol">...</a> <a id="15738" class="Symbol">|</a> <a id="15740" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#668" class="InductiveConstructor">no</a>  <a id="15744" class="Symbol">_</a>          <a id="15755" class="Symbol">=</a>  <a id="15758" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3854" class="InductiveConstructor Operator">ƛ</a> <a id="15760" class="Bound">x</a> <a id="15762" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a> <a id="15764" class="Bound">N</a> <a id="15766" href="plfa.part2.Lambda.html#15554" class="Function Operator">[</a> <a id="15768" class="Bound">y</a> <a id="15770" href="plfa.part2.Lambda.html#15554" class="Function Operator">:=</a> <a id="15773" class="Bound">V</a> <a id="15775" href="plfa.part2.Lambda.html#15554" class="Function Operator">]</a>
<a id="15777" class="Symbol">(</a><a id="15778" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#15778" class="Bound">L</a> <a id="15780" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="15782" href="plfa.part2.Lambda.html#15782" class="Bound">M</a><a id="15783" class="Symbol">)</a> <a id="15785" href="plfa.part2.Lambda.html#15554" class="Function Operator">[</a> <a id="15787" href="plfa.part2.Lambda.html#15787" class="Bound">y</a> <a id="15789" href="plfa.part2.Lambda.html#15554" class="Function Operator">:=</a> <a id="15792" href="plfa.part2.Lambda.html#15792" class="Bound">V</a> <a id="15794" href="plfa.part2.Lambda.html#15554" class="Function Operator">]</a>   <a id="15798" class="Symbol">=</a>  <a id="15801" href="plfa.part2.Lambda.html#15778" class="Bound">L</a> <a id="15803" href="plfa.part2.Lambda.html#15554" class="Function Operator">[</a> <a id="15805" href="plfa.part2.Lambda.html#15787" class="Bound">y</a> <a id="15807" href="plfa.part2.Lambda.html#15554" class="Function Operator">:=</a> <a id="15810" href="plfa.part2.Lambda.html#15792" class="Bound">V</a> <a id="15812" href="plfa.part2.Lambda.html#15554" class="Function Operator">]</a> <a id="15814" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="15816" href="plfa.part2.Lambda.html#15782" class="Bound">M</a> <a id="15818" href="plfa.part2.Lambda.html#15554" class="Function Operator">[</a> <a id="15820" href="plfa.part2.Lambda.html#15787" class="Bound">y</a> <a id="15822" href="plfa.part2.Lambda.html#15554" class="Function Operator">:=</a> <a id="15825" href="plfa.part2.Lambda.html#15792" class="Bound">V</a> <a id="15827" href="plfa.part2.Lambda.html#15554" class="Function Operator">]</a>
<a id="15829" class="Symbol">(</a><a id="15830" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3948" class="InductiveConstructor">`zero</a><a id="15835" class="Symbol">)</a> <a id="15837" href="plfa.part2.Lambda.html#15554" class="Function Operator">[</a> <a id="15839" href="plfa.part2.Lambda.html#15839" class="Bound">y</a> <a id="15841" href="plfa.part2.Lambda.html#15554" class="Function Operator">:=</a> <a id="15844" href="plfa.part2.Lambda.html#15844" class="Bound">V</a> <a id="15846" href="plfa.part2.Lambda.html#15554" class="Function Operator">]</a>   <a id="15850" class="Symbol">=</a>  <a id="15853" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a>
<a id="15859" class="Symbol">(</a><a id="15860" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3982" class="InductiveConstructor Operator">`suc</a> <a id="15865" href="plfa.part2.Lambda.html#15865" class="Bound">M</a><a id="15866" class="Symbol">)</a> <a id="15868" href="plfa.part2.Lambda.html#15554" class="Function Operator">[</a> <a id="15870" href="plfa.part2.Lambda.html#15870" class="Bound">y</a> <a id="15872" href="plfa.part2.Lambda.html#15554" class="Function Operator">:=</a> <a id="15875" href="plfa.part2.Lambda.html#15875" class="Bound">V</a> <a id="15877" href="plfa.part2.Lambda.html#15554" class="Function Operator">]</a>  <a id="15880" class="Symbol">=</a>  <a id="15883" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="15888" href="plfa.part2.Lambda.html#15865" class="Bound">M</a> <a id="15890" href="plfa.part2.Lambda.html#15554" class="Function Operator">[</a> <a id="15892" href="plfa.part2.Lambda.html#15870" class="Bound">y</a> <a id="15894" href="plfa.part2.Lambda.html#15554" class="Function Operator">:=</a> <a id="15897" href="plfa.part2.Lambda.html#15875" class="Bound">V</a> <a id="15899" href="plfa.part2.Lambda.html#15554" class="Function Operator">]</a>
<a id="15901" class="Symbol">(</a><a id="15902" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#4023" class="InductiveConstructor Operator">case</a> <a id="15907" href="plfa.part2.Lambda.html#15907" class="Bound">L</a> <a id="15909" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">[zero⇒</a> <a id="15916" href="plfa.part2.Lambda.html#15916" class="Bound">M</a> <a id="15918" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">|suc</a> <a id="15923" href="plfa.part2.Lambda.html#15923" class="Bound">x</a> <a id="15925" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">⇒</a> <a id="15927" href="plfa.part2.Lambda.html#15927" class="Bound">N</a> <a id="15929" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">]</a><a id="15930" class="Symbol">)</a> <a id="15932" href="plfa.part2.Lambda.html#15554" class="Function Operator">[</a> <a id="15934" href="plfa.part2.Lambda.html#15934" class="Bound">y</a> <a id="15936" href="plfa.part2.Lambda.html#15554" class="Function Operator">:=</a> <a id="15939" href="plfa.part2.Lambda.html#15939" class="Bound">V</a> <a id="15941" href="plfa.part2.Lambda.html#15554" class="Function Operator">]</a> <a id="15943" class="Keyword">with</a> <a id="15948" href="plfa.part2.Lambda.html#15923" class="Bound">x</a> <a id="15950" href="https://agda.github.io/agda-stdlib/v1.1/Data.String.Properties.html#2569" class="Function Operator">≟</a> <a id="15952" href="plfa.part2.Lambda.html#15934" class="Bound">y</a>
<a id="15954" class="Symbol">...</a> <a id="15958" class="Symbol">|</a> <a id="15960" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#641" class="InductiveConstructor">yes</a> <a id="15964" class="Symbol">_</a>          <a id="15975" class="Symbol">=</a>  <a id="15978" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#4023" class="InductiveConstructor Operator">case</a> <a id="15983" class="Bound">L</a> <a id="15985" href="plfa.part2.Lambda.html#15554" class="Function Operator">[</a> <a id="15987" class="Bound">y</a> <a id="15989" href="plfa.part2.Lambda.html#15554" class="Function Operator">:=</a> <a id="15992" class="Bound">V</a> <a id="15994" href="plfa.part2.Lambda.html#15554" class="Function Operator">]</a> <a id="15996" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">[zero⇒</a> <a id="16003" class="Bound">M</a> <a id="16005" href="plfa.part2.Lambda.html#15554" class="Function Operator">[</a> <a id="16007" class="Bound">y</a> <a id="16009" href="plfa.part2.Lambda.html#15554" class="Function Operator">:=</a> <a id="16012" class="Bound">V</a> <a id="16014" href="plfa.part2.Lambda.html#15554" class="Function Operator">]</a> <a id="16016" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">|suc</a> <a id="16021" class="Bound">x</a> <a id="16023" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">⇒</a> <a id="16025" class="Bound">N</a> <a id="16027" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">]</a>
<a id="16029" class="Symbol">...</a> <a id="16033" class="Symbol">|</a> <a id="16035" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#668" class="InductiveConstructor">no</a>  <a id="16039" class="Symbol">_</a>          <a id="16050" class="Symbol">=</a>  <a id="16053" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#4023" class="InductiveConstructor Operator">case</a> <a id="16058" class="Bound">L</a> <a id="16060" href="plfa.part2.Lambda.html#15554" class="Function Operator">[</a> <a id="16062" class="Bound">y</a> <a id="16064" href="plfa.part2.Lambda.html#15554" class="Function Operator">:=</a> <a id="16067" class="Bound">V</a> <a id="16069" href="plfa.part2.Lambda.html#15554" class="Function Operator">]</a> <a id="16071" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">[zero⇒</a> <a id="16078" class="Bound">M</a> <a id="16080" href="plfa.part2.Lambda.html#15554" class="Function Operator">[</a> <a id="16082" class="Bound">y</a> <a id="16084" href="plfa.part2.Lambda.html#15554" class="Function Operator">:=</a> <a id="16087" class="Bound">V</a> <a id="16089" href="plfa.part2.Lambda.html#15554" class="Function Operator">]</a> <a id="16091" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">|suc</a> <a id="16096" class="Bound">x</a> <a id="16098" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">⇒</a> <a id="16100" class="Bound">N</a> <a id="16102" href="plfa.part2.Lambda.html#15554" class="Function Operator">[</a> <a id="16104" class="Bound">y</a> <a id="16106" href="plfa.part2.Lambda.html#15554" class="Function Operator">:=</a> <a id="16109" class="Bound">V</a> <a id="16111" href="plfa.part2.Lambda.html#15554" class="Function Operator">]</a> <a id="16113" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">]</a>
<a id="16115" class="Symbol">(</a><a id="16116" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#4083" class="InductiveConstructor Operator">μ</a> <a id="16118" href="plfa.part2.Lambda.html#16118" class="Bound">x</a> <a id="16120" href="plfa.part2.Lambda.html#4083" class="InductiveConstructor Operator">⇒</a> <a id="16122" href="plfa.part2.Lambda.html#16122" class="Bound">N</a><a id="16123" class="Symbol">)</a> <a id="16125" href="plfa.part2.Lambda.html#15554" class="Function Operator">[</a> <a id="16127" href="plfa.part2.Lambda.html#16127" class="Bound">y</a> <a id="16129" href="plfa.part2.Lambda.html#15554" class="Function Operator">:=</a> <a id="16132" href="plfa.part2.Lambda.html#16132" class="Bound">V</a> <a id="16134" href="plfa.part2.Lambda.html#15554" class="Function Operator">]</a> <a id="16136" class="Keyword">with</a> <a id="16141" href="plfa.part2.Lambda.html#16118" class="Bound">x</a> <a id="16143" href="https://agda.github.io/agda-stdlib/v1.1/Data.String.Properties.html#2569" class="Function Operator">≟</a> <a id="16145" href="plfa.part2.Lambda.html#16127" class="Bound">y</a>
<a id="16147" class="Symbol">...</a> <a id="16151" class="Symbol">|</a> <a id="16153" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#641" class="InductiveConstructor">yes</a> <a id="16157" class="Symbol">_</a>          <a id="16168" class="Symbol">=</a>  <a id="16171" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#4083" class="InductiveConstructor Operator">μ</a> <a id="16173" class="Bound">x</a> <a id="16175" href="plfa.part2.Lambda.html#4083" class="InductiveConstructor Operator">⇒</a> <a id="16177" class="Bound">N</a>
<a id="16179" class="Symbol">...</a> <a id="16183" class="Symbol">|</a> <a id="16185" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#668" class="InductiveConstructor">no</a>  <a id="16189" class="Symbol">_</a>          <a id="16200" class="Symbol">=</a>  <a id="16203" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#4083" class="InductiveConstructor Operator">μ</a> <a id="16205" class="Bound">x</a> <a id="16207" href="plfa.part2.Lambda.html#4083" class="InductiveConstructor Operator">⇒</a> <a id="16209" class="Bound">N</a> <a id="16211" href="plfa.part2.Lambda.html#15554" class="Function Operator">[</a> <a id="16213" class="Bound">y</a> <a id="16215" href="plfa.part2.Lambda.html#15554" class="Function Operator">:=</a> <a id="16218" class="Bound">V</a> <a id="16220" href="plfa.part2.Lambda.html#15554" class="Function Operator">]</a>
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

{% raw %}<pre class="Agda"><a id="16987" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#16987" class="Function">_</a> <a id="16989" class="Symbol">:</a> <a id="16991" class="Symbol">(</a><a id="16992" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">ƛ</a> <a id="16994" class="String">&quot;z&quot;</a> <a id="16998" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a> <a id="17000" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="17002" class="String">&quot;s&quot;</a> <a id="17006" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="17008" class="Symbol">(</a><a id="17009" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="17011" class="String">&quot;s&quot;</a> <a id="17015" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="17017" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="17019" class="String">&quot;z&quot;</a><a id="17022" class="Symbol">))</a> <a id="17025" href="plfa.part2.Lambda.html#15554" class="Function Operator">[</a> <a id="17027" class="String">&quot;s&quot;</a> <a id="17031" href="plfa.part2.Lambda.html#15554" class="Function Operator">:=</a> <a id="17034" href="plfa.part2.Lambda.html#5938" class="Function">sucᶜ</a> <a id="17039" href="plfa.part2.Lambda.html#15554" class="Function Operator">]</a> <a id="17041" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="17043" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">ƛ</a> <a id="17045" class="String">&quot;z&quot;</a> <a id="17049" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a> <a id="17051" href="plfa.part2.Lambda.html#5938" class="Function">sucᶜ</a> <a id="17056" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="17058" class="Symbol">(</a><a id="17059" href="plfa.part2.Lambda.html#5938" class="Function">sucᶜ</a> <a id="17064" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="17066" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="17068" class="String">&quot;z&quot;</a><a id="17071" class="Symbol">)</a>
<a id="17073" class="Symbol">_</a> <a id="17075" class="Symbol">=</a> <a id="17077" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>

<a id="17083" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#17083" class="Function">_</a> <a id="17085" class="Symbol">:</a> <a id="17087" class="Symbol">(</a><a id="17088" href="plfa.part2.Lambda.html#5938" class="Function">sucᶜ</a> <a id="17093" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="17095" class="Symbol">(</a><a id="17096" href="plfa.part2.Lambda.html#5938" class="Function">sucᶜ</a> <a id="17101" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="17103" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="17105" class="String">&quot;z&quot;</a><a id="17108" class="Symbol">))</a> <a id="17111" href="plfa.part2.Lambda.html#15554" class="Function Operator">[</a> <a id="17113" class="String">&quot;z&quot;</a> <a id="17117" href="plfa.part2.Lambda.html#15554" class="Function Operator">:=</a> <a id="17120" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a> <a id="17126" href="plfa.part2.Lambda.html#15554" class="Function Operator">]</a> <a id="17128" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="17130" href="plfa.part2.Lambda.html#5938" class="Function">sucᶜ</a> <a id="17135" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="17137" class="Symbol">(</a><a id="17138" href="plfa.part2.Lambda.html#5938" class="Function">sucᶜ</a> <a id="17143" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="17145" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a><a id="17150" class="Symbol">)</a>
<a id="17152" class="Symbol">_</a> <a id="17154" class="Symbol">=</a> <a id="17156" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>

<a id="17162" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#17162" class="Function">_</a> <a id="17164" class="Symbol">:</a> <a id="17166" class="Symbol">(</a><a id="17167" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">ƛ</a> <a id="17169" class="String">&quot;x&quot;</a> <a id="17173" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a> <a id="17175" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="17177" class="String">&quot;y&quot;</a><a id="17180" class="Symbol">)</a> <a id="17182" href="plfa.part2.Lambda.html#15554" class="Function Operator">[</a> <a id="17184" class="String">&quot;y&quot;</a> <a id="17188" href="plfa.part2.Lambda.html#15554" class="Function Operator">:=</a> <a id="17191" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a> <a id="17197" href="plfa.part2.Lambda.html#15554" class="Function Operator">]</a> <a id="17199" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="17201" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">ƛ</a> <a id="17203" class="String">&quot;x&quot;</a> <a id="17207" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a> <a id="17209" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a>
<a id="17215" class="Symbol">_</a> <a id="17217" class="Symbol">=</a> <a id="17219" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>

<a id="17225" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#17225" class="Function">_</a> <a id="17227" class="Symbol">:</a> <a id="17229" class="Symbol">(</a><a id="17230" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">ƛ</a> <a id="17232" class="String">&quot;x&quot;</a> <a id="17236" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a> <a id="17238" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="17240" class="String">&quot;x&quot;</a><a id="17243" class="Symbol">)</a> <a id="17245" href="plfa.part2.Lambda.html#15554" class="Function Operator">[</a> <a id="17247" class="String">&quot;x&quot;</a> <a id="17251" href="plfa.part2.Lambda.html#15554" class="Function Operator">:=</a> <a id="17254" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a> <a id="17260" href="plfa.part2.Lambda.html#15554" class="Function Operator">]</a> <a id="17262" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="17264" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">ƛ</a> <a id="17266" class="String">&quot;x&quot;</a> <a id="17270" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a> <a id="17272" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="17274" class="String">&quot;x&quot;</a>
<a id="17278" class="Symbol">_</a> <a id="17280" class="Symbol">=</a> <a id="17282" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>

<a id="17288" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#17288" class="Function">_</a> <a id="17290" class="Symbol">:</a> <a id="17292" class="Symbol">(</a><a id="17293" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">ƛ</a> <a id="17295" class="String">&quot;y&quot;</a> <a id="17299" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a> <a id="17301" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="17303" class="String">&quot;y&quot;</a><a id="17306" class="Symbol">)</a> <a id="17308" href="plfa.part2.Lambda.html#15554" class="Function Operator">[</a> <a id="17310" class="String">&quot;x&quot;</a> <a id="17314" href="plfa.part2.Lambda.html#15554" class="Function Operator">:=</a> <a id="17317" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a> <a id="17323" href="plfa.part2.Lambda.html#15554" class="Function Operator">]</a> <a id="17325" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="17327" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">ƛ</a> <a id="17329" class="String">&quot;y&quot;</a> <a id="17333" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a> <a id="17335" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="17337" class="String">&quot;y&quot;</a>
<a id="17341" class="Symbol">_</a> <a id="17343" class="Symbol">=</a> <a id="17345" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>
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

{% raw %}<pre class="Agda"><a id="17968" class="Comment">-- Your code goes here</a>
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

{% raw %}<pre class="Agda"><a id="20176" class="Keyword">infix</a> <a id="20182" class="Number">4</a> <a id="20184" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#20195" class="Datatype Operator">_—→_</a>

<a id="20190" class="Keyword">data</a> <a id="_—→_"></a><a id="20195" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#20195" class="Datatype Operator">_—→_</a> <a id="20200" class="Symbol">:</a> <a id="20202" href="plfa.part2.Lambda.html#3796" class="Datatype">Term</a> <a id="20207" class="Symbol">→</a> <a id="20209" href="plfa.part2.Lambda.html#3796" class="Datatype">Term</a> <a id="20214" class="Symbol">→</a> <a id="20216" class="PrimitiveType">Set</a> <a id="20220" class="Keyword">where</a>

  <a id="_—→_.ξ-·₁"></a><a id="20229" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#20229" class="InductiveConstructor">ξ-·₁</a> <a id="20234" class="Symbol">:</a> <a id="20236" class="Symbol">∀</a> <a id="20238" class="Symbol">{</a><a id="20239" href="plfa.part2.Lambda.html#20239" class="Bound">L</a> <a id="20241" href="plfa.part2.Lambda.html#20241" class="Bound">L′</a> <a id="20244" href="plfa.part2.Lambda.html#20244" class="Bound">M</a><a id="20245" class="Symbol">}</a>
    <a id="20251" class="Symbol">→</a> <a id="20253" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#20239" class="Bound">L</a> <a id="20255" href="plfa.part2.Lambda.html#20195" class="Datatype Operator">—→</a> <a id="20258" href="plfa.part2.Lambda.html#20241" class="Bound">L′</a>
      <a id="20267" class="Comment">-----------------</a>
    <a id="20289" class="Symbol">→</a> <a id="20291" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#20239" class="Bound">L</a> <a id="20293" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="20295" href="plfa.part2.Lambda.html#20244" class="Bound">M</a> <a id="20297" href="plfa.part2.Lambda.html#20195" class="Datatype Operator">—→</a> <a id="20300" href="plfa.part2.Lambda.html#20241" class="Bound">L′</a> <a id="20303" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="20305" href="plfa.part2.Lambda.html#20244" class="Bound">M</a>

  <a id="_—→_.ξ-·₂"></a><a id="20310" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#20310" class="InductiveConstructor">ξ-·₂</a> <a id="20315" class="Symbol">:</a> <a id="20317" class="Symbol">∀</a> <a id="20319" class="Symbol">{</a><a id="20320" href="plfa.part2.Lambda.html#20320" class="Bound">V</a> <a id="20322" href="plfa.part2.Lambda.html#20322" class="Bound">M</a> <a id="20324" href="plfa.part2.Lambda.html#20324" class="Bound">M′</a><a id="20326" class="Symbol">}</a>
    <a id="20332" class="Symbol">→</a> <a id="20334" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#12171" class="Datatype">Value</a> <a id="20340" href="plfa.part2.Lambda.html#20320" class="Bound">V</a>
    <a id="20346" class="Symbol">→</a> <a id="20348" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#20322" class="Bound">M</a> <a id="20350" href="plfa.part2.Lambda.html#20195" class="Datatype Operator">—→</a> <a id="20353" href="plfa.part2.Lambda.html#20324" class="Bound">M′</a>
      <a id="20362" class="Comment">-----------------</a>
    <a id="20384" class="Symbol">→</a> <a id="20386" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#20320" class="Bound">V</a> <a id="20388" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="20390" href="plfa.part2.Lambda.html#20322" class="Bound">M</a> <a id="20392" href="plfa.part2.Lambda.html#20195" class="Datatype Operator">—→</a> <a id="20395" href="plfa.part2.Lambda.html#20320" class="Bound">V</a> <a id="20397" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="20399" href="plfa.part2.Lambda.html#20324" class="Bound">M′</a>

  <a id="_—→_.β-ƛ"></a><a id="20405" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#20405" class="InductiveConstructor">β-ƛ</a> <a id="20409" class="Symbol">:</a> <a id="20411" class="Symbol">∀</a> <a id="20413" class="Symbol">{</a><a id="20414" href="plfa.part2.Lambda.html#20414" class="Bound">x</a> <a id="20416" href="plfa.part2.Lambda.html#20416" class="Bound">N</a> <a id="20418" href="plfa.part2.Lambda.html#20418" class="Bound">V</a><a id="20419" class="Symbol">}</a>
    <a id="20425" class="Symbol">→</a> <a id="20427" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#12171" class="Datatype">Value</a> <a id="20433" href="plfa.part2.Lambda.html#20418" class="Bound">V</a>
      <a id="20441" class="Comment">------------------------------</a>
    <a id="20476" class="Symbol">→</a> <a id="20478" class="Symbol">(</a><a id="20479" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3854" class="InductiveConstructor Operator">ƛ</a> <a id="20481" href="plfa.part2.Lambda.html#20414" class="Bound">x</a> <a id="20483" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a> <a id="20485" href="plfa.part2.Lambda.html#20416" class="Bound">N</a><a id="20486" class="Symbol">)</a> <a id="20488" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="20490" href="plfa.part2.Lambda.html#20418" class="Bound">V</a> <a id="20492" href="plfa.part2.Lambda.html#20195" class="Datatype Operator">—→</a> <a id="20495" href="plfa.part2.Lambda.html#20416" class="Bound">N</a> <a id="20497" href="plfa.part2.Lambda.html#15554" class="Function Operator">[</a> <a id="20499" href="plfa.part2.Lambda.html#20414" class="Bound">x</a> <a id="20501" href="plfa.part2.Lambda.html#15554" class="Function Operator">:=</a> <a id="20504" href="plfa.part2.Lambda.html#20418" class="Bound">V</a> <a id="20506" href="plfa.part2.Lambda.html#15554" class="Function Operator">]</a>

  <a id="_—→_.ξ-suc"></a><a id="20511" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#20511" class="InductiveConstructor">ξ-suc</a> <a id="20517" class="Symbol">:</a> <a id="20519" class="Symbol">∀</a> <a id="20521" class="Symbol">{</a><a id="20522" href="plfa.part2.Lambda.html#20522" class="Bound">M</a> <a id="20524" href="plfa.part2.Lambda.html#20524" class="Bound">M′</a><a id="20526" class="Symbol">}</a>
    <a id="20532" class="Symbol">→</a> <a id="20534" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#20522" class="Bound">M</a> <a id="20536" href="plfa.part2.Lambda.html#20195" class="Datatype Operator">—→</a> <a id="20539" href="plfa.part2.Lambda.html#20524" class="Bound">M′</a>
      <a id="20548" class="Comment">------------------</a>
    <a id="20571" class="Symbol">→</a> <a id="20573" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3982" class="InductiveConstructor Operator">`suc</a> <a id="20578" href="plfa.part2.Lambda.html#20522" class="Bound">M</a> <a id="20580" href="plfa.part2.Lambda.html#20195" class="Datatype Operator">—→</a> <a id="20583" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="20588" href="plfa.part2.Lambda.html#20524" class="Bound">M′</a>

  <a id="_—→_.ξ-case"></a><a id="20594" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#20594" class="InductiveConstructor">ξ-case</a> <a id="20601" class="Symbol">:</a> <a id="20603" class="Symbol">∀</a> <a id="20605" class="Symbol">{</a><a id="20606" href="plfa.part2.Lambda.html#20606" class="Bound">x</a> <a id="20608" href="plfa.part2.Lambda.html#20608" class="Bound">L</a> <a id="20610" href="plfa.part2.Lambda.html#20610" class="Bound">L′</a> <a id="20613" href="plfa.part2.Lambda.html#20613" class="Bound">M</a> <a id="20615" href="plfa.part2.Lambda.html#20615" class="Bound">N</a><a id="20616" class="Symbol">}</a>
    <a id="20622" class="Symbol">→</a> <a id="20624" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#20608" class="Bound">L</a> <a id="20626" href="plfa.part2.Lambda.html#20195" class="Datatype Operator">—→</a> <a id="20629" href="plfa.part2.Lambda.html#20610" class="Bound">L′</a>
      <a id="20638" class="Comment">-----------------------------------------------------------------</a>
    <a id="20708" class="Symbol">→</a> <a id="20710" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#4023" class="InductiveConstructor Operator">case</a> <a id="20715" href="plfa.part2.Lambda.html#20608" class="Bound">L</a> <a id="20717" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">[zero⇒</a> <a id="20724" href="plfa.part2.Lambda.html#20613" class="Bound">M</a> <a id="20726" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">|suc</a> <a id="20731" href="plfa.part2.Lambda.html#20606" class="Bound">x</a> <a id="20733" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">⇒</a> <a id="20735" href="plfa.part2.Lambda.html#20615" class="Bound">N</a> <a id="20737" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">]</a> <a id="20739" href="plfa.part2.Lambda.html#20195" class="Datatype Operator">—→</a> <a id="20742" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">case</a> <a id="20747" href="plfa.part2.Lambda.html#20610" class="Bound">L′</a> <a id="20750" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">[zero⇒</a> <a id="20757" href="plfa.part2.Lambda.html#20613" class="Bound">M</a> <a id="20759" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">|suc</a> <a id="20764" href="plfa.part2.Lambda.html#20606" class="Bound">x</a> <a id="20766" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">⇒</a> <a id="20768" href="plfa.part2.Lambda.html#20615" class="Bound">N</a> <a id="20770" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">]</a>

  <a id="_—→_.β-zero"></a><a id="20775" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#20775" class="InductiveConstructor">β-zero</a> <a id="20782" class="Symbol">:</a> <a id="20784" class="Symbol">∀</a> <a id="20786" class="Symbol">{</a><a id="20787" href="plfa.part2.Lambda.html#20787" class="Bound">x</a> <a id="20789" href="plfa.part2.Lambda.html#20789" class="Bound">M</a> <a id="20791" href="plfa.part2.Lambda.html#20791" class="Bound">N</a><a id="20792" class="Symbol">}</a>
      <a id="20800" class="Comment">----------------------------------------</a>
    <a id="20845" class="Symbol">→</a> <a id="20847" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#4023" class="InductiveConstructor Operator">case</a> <a id="20852" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a> <a id="20858" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">[zero⇒</a> <a id="20865" href="plfa.part2.Lambda.html#20789" class="Bound">M</a> <a id="20867" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">|suc</a> <a id="20872" href="plfa.part2.Lambda.html#20787" class="Bound">x</a> <a id="20874" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">⇒</a> <a id="20876" href="plfa.part2.Lambda.html#20791" class="Bound">N</a> <a id="20878" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">]</a> <a id="20880" href="plfa.part2.Lambda.html#20195" class="Datatype Operator">—→</a> <a id="20883" href="plfa.part2.Lambda.html#20789" class="Bound">M</a>

  <a id="_—→_.β-suc"></a><a id="20888" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#20888" class="InductiveConstructor">β-suc</a> <a id="20894" class="Symbol">:</a> <a id="20896" class="Symbol">∀</a> <a id="20898" class="Symbol">{</a><a id="20899" href="plfa.part2.Lambda.html#20899" class="Bound">x</a> <a id="20901" href="plfa.part2.Lambda.html#20901" class="Bound">V</a> <a id="20903" href="plfa.part2.Lambda.html#20903" class="Bound">M</a> <a id="20905" href="plfa.part2.Lambda.html#20905" class="Bound">N</a><a id="20906" class="Symbol">}</a>
    <a id="20912" class="Symbol">→</a> <a id="20914" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#12171" class="Datatype">Value</a> <a id="20920" href="plfa.part2.Lambda.html#20901" class="Bound">V</a>
      <a id="20928" class="Comment">---------------------------------------------------</a>
    <a id="20984" class="Symbol">→</a> <a id="20986" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#4023" class="InductiveConstructor Operator">case</a> <a id="20991" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="20996" href="plfa.part2.Lambda.html#20901" class="Bound">V</a> <a id="20998" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">[zero⇒</a> <a id="21005" href="plfa.part2.Lambda.html#20903" class="Bound">M</a> <a id="21007" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">|suc</a> <a id="21012" href="plfa.part2.Lambda.html#20899" class="Bound">x</a> <a id="21014" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">⇒</a> <a id="21016" href="plfa.part2.Lambda.html#20905" class="Bound">N</a> <a id="21018" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">]</a> <a id="21020" href="plfa.part2.Lambda.html#20195" class="Datatype Operator">—→</a> <a id="21023" href="plfa.part2.Lambda.html#20905" class="Bound">N</a> <a id="21025" href="plfa.part2.Lambda.html#15554" class="Function Operator">[</a> <a id="21027" href="plfa.part2.Lambda.html#20899" class="Bound">x</a> <a id="21029" href="plfa.part2.Lambda.html#15554" class="Function Operator">:=</a> <a id="21032" href="plfa.part2.Lambda.html#20901" class="Bound">V</a> <a id="21034" href="plfa.part2.Lambda.html#15554" class="Function Operator">]</a>

  <a id="_—→_.β-μ"></a><a id="21039" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#21039" class="InductiveConstructor">β-μ</a> <a id="21043" class="Symbol">:</a> <a id="21045" class="Symbol">∀</a> <a id="21047" class="Symbol">{</a><a id="21048" href="plfa.part2.Lambda.html#21048" class="Bound">x</a> <a id="21050" href="plfa.part2.Lambda.html#21050" class="Bound">M</a><a id="21051" class="Symbol">}</a>
      <a id="21059" class="Comment">------------------------------</a>
    <a id="21094" class="Symbol">→</a> <a id="21096" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#4083" class="InductiveConstructor Operator">μ</a> <a id="21098" href="plfa.part2.Lambda.html#21048" class="Bound">x</a> <a id="21100" href="plfa.part2.Lambda.html#4083" class="InductiveConstructor Operator">⇒</a> <a id="21102" href="plfa.part2.Lambda.html#21050" class="Bound">M</a> <a id="21104" href="plfa.part2.Lambda.html#20195" class="Datatype Operator">—→</a> <a id="21107" href="plfa.part2.Lambda.html#21050" class="Bound">M</a> <a id="21109" href="plfa.part2.Lambda.html#15554" class="Function Operator">[</a> <a id="21111" href="plfa.part2.Lambda.html#21048" class="Bound">x</a> <a id="21113" href="plfa.part2.Lambda.html#15554" class="Function Operator">:=</a> <a id="21116" href="plfa.part2.Lambda.html#4083" class="InductiveConstructor Operator">μ</a> <a id="21118" href="plfa.part2.Lambda.html#21048" class="Bound">x</a> <a id="21120" href="plfa.part2.Lambda.html#4083" class="InductiveConstructor Operator">⇒</a> <a id="21122" href="plfa.part2.Lambda.html#21050" class="Bound">M</a> <a id="21124" href="plfa.part2.Lambda.html#15554" class="Function Operator">]</a>
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
{% raw %}<pre class="Agda"><a id="23120" class="Keyword">infix</a>  <a id="23127" class="Number">2</a> <a id="23129" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23185" class="Datatype Operator">_—↠_</a>
<a id="23134" class="Keyword">infix</a>  <a id="23141" class="Number">1</a> <a id="23143" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23335" class="Function Operator">begin_</a>
<a id="23150" class="Keyword">infixr</a> <a id="23157" class="Number">2</a> <a id="23159" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23259" class="InductiveConstructor Operator">_—→⟨_⟩_</a>
<a id="23167" class="Keyword">infix</a>  <a id="23174" class="Number">3</a> <a id="23176" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23218" class="InductiveConstructor Operator">_∎</a>

<a id="23180" class="Keyword">data</a> <a id="_—↠_"></a><a id="23185" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23185" class="Datatype Operator">_—↠_</a> <a id="23190" class="Symbol">:</a> <a id="23192" href="plfa.part2.Lambda.html#3796" class="Datatype">Term</a> <a id="23197" class="Symbol">→</a> <a id="23199" href="plfa.part2.Lambda.html#3796" class="Datatype">Term</a> <a id="23204" class="Symbol">→</a> <a id="23206" class="PrimitiveType">Set</a> <a id="23210" class="Keyword">where</a>
  <a id="_—↠_._∎"></a><a id="23218" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23218" class="InductiveConstructor Operator">_∎</a> <a id="23221" class="Symbol">:</a> <a id="23223" class="Symbol">∀</a> <a id="23225" href="plfa.part2.Lambda.html#23225" class="Bound">M</a>
      <a id="23233" class="Comment">---------</a>
    <a id="23247" class="Symbol">→</a> <a id="23249" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23225" class="Bound">M</a> <a id="23251" href="plfa.part2.Lambda.html#23185" class="Datatype Operator">—↠</a> <a id="23254" href="plfa.part2.Lambda.html#23225" class="Bound">M</a>

  <a id="_—↠_._—→⟨_⟩_"></a><a id="23259" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23259" class="InductiveConstructor Operator">_—→⟨_⟩_</a> <a id="23267" class="Symbol">:</a> <a id="23269" class="Symbol">∀</a> <a id="23271" href="plfa.part2.Lambda.html#23271" class="Bound">L</a> <a id="23273" class="Symbol">{</a><a id="23274" href="plfa.part2.Lambda.html#23274" class="Bound">M</a> <a id="23276" href="plfa.part2.Lambda.html#23276" class="Bound">N</a><a id="23277" class="Symbol">}</a>
    <a id="23283" class="Symbol">→</a> <a id="23285" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23271" class="Bound">L</a> <a id="23287" href="plfa.part2.Lambda.html#20195" class="Datatype Operator">—→</a> <a id="23290" href="plfa.part2.Lambda.html#23274" class="Bound">M</a>
    <a id="23296" class="Symbol">→</a> <a id="23298" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23274" class="Bound">M</a> <a id="23300" href="plfa.part2.Lambda.html#23185" class="Datatype Operator">—↠</a> <a id="23303" href="plfa.part2.Lambda.html#23276" class="Bound">N</a>
      <a id="23311" class="Comment">---------</a>
    <a id="23325" class="Symbol">→</a> <a id="23327" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23271" class="Bound">L</a> <a id="23329" href="plfa.part2.Lambda.html#23185" class="Datatype Operator">—↠</a> <a id="23332" href="plfa.part2.Lambda.html#23276" class="Bound">N</a>

<a id="begin_"></a><a id="23335" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23335" class="Function Operator">begin_</a> <a id="23342" class="Symbol">:</a> <a id="23344" class="Symbol">∀</a> <a id="23346" class="Symbol">{</a><a id="23347" href="plfa.part2.Lambda.html#23347" class="Bound">M</a> <a id="23349" href="plfa.part2.Lambda.html#23349" class="Bound">N</a><a id="23350" class="Symbol">}</a>
  <a id="23354" class="Symbol">→</a> <a id="23356" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23347" class="Bound">M</a> <a id="23358" href="plfa.part2.Lambda.html#23185" class="Datatype Operator">—↠</a> <a id="23361" href="plfa.part2.Lambda.html#23349" class="Bound">N</a>
    <a id="23367" class="Comment">------</a>
  <a id="23376" class="Symbol">→</a> <a id="23378" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23347" class="Bound">M</a> <a id="23380" href="plfa.part2.Lambda.html#23185" class="Datatype Operator">—↠</a> <a id="23383" href="plfa.part2.Lambda.html#23349" class="Bound">N</a>
<a id="23385" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23335" class="Function Operator">begin</a> <a id="23391" href="plfa.part2.Lambda.html#23391" class="Bound">M—↠N</a> <a id="23396" class="Symbol">=</a> <a id="23398" href="plfa.part2.Lambda.html#23391" class="Bound">M—↠N</a>
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
{% raw %}<pre class="Agda"><a id="24081" class="Keyword">data</a> <a id="_—↠′_"></a><a id="24086" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#24086" class="Datatype Operator">_—↠′_</a> <a id="24092" class="Symbol">:</a> <a id="24094" href="plfa.part2.Lambda.html#3796" class="Datatype">Term</a> <a id="24099" class="Symbol">→</a> <a id="24101" href="plfa.part2.Lambda.html#3796" class="Datatype">Term</a> <a id="24106" class="Symbol">→</a> <a id="24108" class="PrimitiveType">Set</a> <a id="24112" class="Keyword">where</a>

  <a id="_—↠′_.step′"></a><a id="24121" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#24121" class="InductiveConstructor">step′</a> <a id="24127" class="Symbol">:</a> <a id="24129" class="Symbol">∀</a> <a id="24131" class="Symbol">{</a><a id="24132" href="plfa.part2.Lambda.html#24132" class="Bound">M</a> <a id="24134" href="plfa.part2.Lambda.html#24134" class="Bound">N</a><a id="24135" class="Symbol">}</a>
    <a id="24141" class="Symbol">→</a> <a id="24143" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#24132" class="Bound">M</a> <a id="24145" href="plfa.part2.Lambda.html#20195" class="Datatype Operator">—→</a> <a id="24148" href="plfa.part2.Lambda.html#24134" class="Bound">N</a>
      <a id="24156" class="Comment">-------</a>
    <a id="24168" class="Symbol">→</a> <a id="24170" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#24132" class="Bound">M</a> <a id="24172" href="plfa.part2.Lambda.html#24086" class="Datatype Operator">—↠′</a> <a id="24176" href="plfa.part2.Lambda.html#24134" class="Bound">N</a>

  <a id="_—↠′_.refl′"></a><a id="24181" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#24181" class="InductiveConstructor">refl′</a> <a id="24187" class="Symbol">:</a> <a id="24189" class="Symbol">∀</a> <a id="24191" class="Symbol">{</a><a id="24192" href="plfa.part2.Lambda.html#24192" class="Bound">M</a><a id="24193" class="Symbol">}</a>
      <a id="24201" class="Comment">-------</a>
    <a id="24213" class="Symbol">→</a> <a id="24215" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#24192" class="Bound">M</a> <a id="24217" href="plfa.part2.Lambda.html#24086" class="Datatype Operator">—↠′</a> <a id="24221" href="plfa.part2.Lambda.html#24192" class="Bound">M</a>

  <a id="_—↠′_.trans′"></a><a id="24226" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#24226" class="InductiveConstructor">trans′</a> <a id="24233" class="Symbol">:</a> <a id="24235" class="Symbol">∀</a> <a id="24237" class="Symbol">{</a><a id="24238" href="plfa.part2.Lambda.html#24238" class="Bound">L</a> <a id="24240" href="plfa.part2.Lambda.html#24240" class="Bound">M</a> <a id="24242" href="plfa.part2.Lambda.html#24242" class="Bound">N</a><a id="24243" class="Symbol">}</a>
    <a id="24249" class="Symbol">→</a> <a id="24251" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#24238" class="Bound">L</a> <a id="24253" href="plfa.part2.Lambda.html#24086" class="Datatype Operator">—↠′</a> <a id="24257" href="plfa.part2.Lambda.html#24240" class="Bound">M</a>
    <a id="24263" class="Symbol">→</a> <a id="24265" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#24240" class="Bound">M</a> <a id="24267" href="plfa.part2.Lambda.html#24086" class="Datatype Operator">—↠′</a> <a id="24271" href="plfa.part2.Lambda.html#24242" class="Bound">N</a>
      <a id="24279" class="Comment">-------</a>
    <a id="24291" class="Symbol">→</a> <a id="24293" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#24238" class="Bound">L</a> <a id="24295" href="plfa.part2.Lambda.html#24086" class="Datatype Operator">—↠′</a> <a id="24299" href="plfa.part2.Lambda.html#24242" class="Bound">N</a>
</pre>{% endraw %}The three constructors specify, respectively, that `—↠′` includes `—→`
and is reflexive and transitive.  A good exercise is to show that
the two definitions are equivalent (indeed, one embeds in the other).

#### Exercise `—↠≲—↠′` (practice)

Show that the first notion of reflexive and transitive closure
above embeds into the second. Why are they not isomorphic?

{% raw %}<pre class="Agda"><a id="24675" class="Comment">-- Your code goes here</a>
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
{% raw %}<pre class="Agda"><a id="26245" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#26245" class="Function">_</a> <a id="26247" class="Symbol">:</a> <a id="26249" href="plfa.part2.Lambda.html#5773" class="Function">twoᶜ</a> <a id="26254" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="26256" href="plfa.part2.Lambda.html#5938" class="Function">sucᶜ</a> <a id="26261" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="26263" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a> <a id="26269" href="plfa.part2.Lambda.html#23185" class="Datatype Operator">—↠</a> <a id="26272" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="26277" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="26282" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a>
<a id="26288" class="Symbol">_</a> <a id="26290" class="Symbol">=</a>
  <a id="26294" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23335" class="Function Operator">begin</a>
    <a id="26304" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#5773" class="Function">twoᶜ</a> <a id="26309" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="26311" href="plfa.part2.Lambda.html#5938" class="Function">sucᶜ</a> <a id="26316" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="26318" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a>
  <a id="26326" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23259" class="InductiveConstructor Operator">—→⟨</a> <a id="26330" href="plfa.part2.Lambda.html#20229" class="InductiveConstructor">ξ-·₁</a> <a id="26335" class="Symbol">(</a><a id="26336" href="plfa.part2.Lambda.html#20405" class="InductiveConstructor">β-ƛ</a> <a id="26340" href="plfa.part2.Lambda.html#12199" class="InductiveConstructor">V-ƛ</a><a id="26343" class="Symbol">)</a> <a id="26345" href="plfa.part2.Lambda.html#23259" class="InductiveConstructor Operator">⟩</a>
    <a id="26351" class="Symbol">(</a><a id="26352" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3854" class="InductiveConstructor Operator">ƛ</a> <a id="26354" class="String">&quot;z&quot;</a> <a id="26358" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a> <a id="26360" href="plfa.part2.Lambda.html#5938" class="Function">sucᶜ</a> <a id="26365" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="26367" class="Symbol">(</a><a id="26368" href="plfa.part2.Lambda.html#5938" class="Function">sucᶜ</a> <a id="26373" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="26375" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="26377" class="String">&quot;z&quot;</a><a id="26380" class="Symbol">))</a> <a id="26383" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="26385" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a>
  <a id="26393" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23259" class="InductiveConstructor Operator">—→⟨</a> <a id="26397" href="plfa.part2.Lambda.html#20405" class="InductiveConstructor">β-ƛ</a> <a id="26401" href="plfa.part2.Lambda.html#12260" class="InductiveConstructor">V-zero</a> <a id="26408" href="plfa.part2.Lambda.html#23259" class="InductiveConstructor Operator">⟩</a>
    <a id="26414" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#5938" class="Function">sucᶜ</a> <a id="26419" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="26421" class="Symbol">(</a><a id="26422" href="plfa.part2.Lambda.html#5938" class="Function">sucᶜ</a> <a id="26427" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="26429" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a><a id="26434" class="Symbol">)</a>
  <a id="26438" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23259" class="InductiveConstructor Operator">—→⟨</a> <a id="26442" href="plfa.part2.Lambda.html#20310" class="InductiveConstructor">ξ-·₂</a> <a id="26447" href="plfa.part2.Lambda.html#12199" class="InductiveConstructor">V-ƛ</a> <a id="26451" class="Symbol">(</a><a id="26452" href="plfa.part2.Lambda.html#20405" class="InductiveConstructor">β-ƛ</a> <a id="26456" href="plfa.part2.Lambda.html#12260" class="InductiveConstructor">V-zero</a><a id="26462" class="Symbol">)</a> <a id="26464" href="plfa.part2.Lambda.html#23259" class="InductiveConstructor Operator">⟩</a>
    <a id="26470" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#5938" class="Function">sucᶜ</a> <a id="26475" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="26477" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="26482" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a>
  <a id="26490" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23259" class="InductiveConstructor Operator">—→⟨</a> <a id="26494" href="plfa.part2.Lambda.html#20405" class="InductiveConstructor">β-ƛ</a> <a id="26498" class="Symbol">(</a><a id="26499" href="plfa.part2.Lambda.html#12308" class="InductiveConstructor">V-suc</a> <a id="26505" href="plfa.part2.Lambda.html#12260" class="InductiveConstructor">V-zero</a><a id="26511" class="Symbol">)</a> <a id="26513" href="plfa.part2.Lambda.html#23259" class="InductiveConstructor Operator">⟩</a>
    <a id="26519" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3982" class="InductiveConstructor Operator">`suc</a> <a id="26524" class="Symbol">(</a><a id="26525" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="26530" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a><a id="26535" class="Symbol">)</a>
  <a id="26539" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23218" class="InductiveConstructor Operator">∎</a>
</pre>{% endraw %}
Here is a sample reduction demonstrating that two plus two is four:
{% raw %}<pre class="Agda"><a id="26618" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#26618" class="Function">_</a> <a id="26620" class="Symbol">:</a> <a id="26622" href="plfa.part2.Lambda.html#4558" class="Function">plus</a> <a id="26627" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="26629" href="plfa.part2.Lambda.html#4524" class="Function">two</a> <a id="26633" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="26635" href="plfa.part2.Lambda.html#4524" class="Function">two</a> <a id="26639" href="plfa.part2.Lambda.html#23185" class="Datatype Operator">—↠</a> <a id="26642" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="26647" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="26652" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="26657" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="26662" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a>
<a id="26668" class="Symbol">_</a> <a id="26670" class="Symbol">=</a>
  <a id="26674" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23335" class="Function Operator">begin</a>
    <a id="26684" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#4558" class="Function">plus</a> <a id="26689" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="26691" href="plfa.part2.Lambda.html#4524" class="Function">two</a> <a id="26695" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="26697" href="plfa.part2.Lambda.html#4524" class="Function">two</a>
  <a id="26703" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23259" class="InductiveConstructor Operator">—→⟨</a> <a id="26707" href="plfa.part2.Lambda.html#20229" class="InductiveConstructor">ξ-·₁</a> <a id="26712" class="Symbol">(</a><a id="26713" href="plfa.part2.Lambda.html#20229" class="InductiveConstructor">ξ-·₁</a> <a id="26718" href="plfa.part2.Lambda.html#21039" class="InductiveConstructor">β-μ</a><a id="26721" class="Symbol">)</a> <a id="26723" href="plfa.part2.Lambda.html#23259" class="InductiveConstructor Operator">⟩</a>
    <a id="26729" class="Symbol">(</a><a id="26730" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3854" class="InductiveConstructor Operator">ƛ</a> <a id="26732" class="String">&quot;m&quot;</a> <a id="26736" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a> <a id="26738" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">ƛ</a> <a id="26740" class="String">&quot;n&quot;</a> <a id="26744" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a>
      <a id="26752" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#4023" class="InductiveConstructor Operator">case</a> <a id="26757" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="26759" class="String">&quot;m&quot;</a> <a id="26763" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">[zero⇒</a> <a id="26770" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="26772" class="String">&quot;n&quot;</a> <a id="26776" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">|suc</a> <a id="26781" class="String">&quot;m&quot;</a> <a id="26785" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">⇒</a> <a id="26787" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="26792" class="Symbol">(</a><a id="26793" href="plfa.part2.Lambda.html#4558" class="Function">plus</a> <a id="26798" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="26800" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="26802" class="String">&quot;m&quot;</a> <a id="26806" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="26808" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="26810" class="String">&quot;n&quot;</a><a id="26813" class="Symbol">)</a> <a id="26815" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">]</a><a id="26816" class="Symbol">)</a>
        <a id="26826" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3900" class="InductiveConstructor Operator">·</a> <a id="26828" href="plfa.part2.Lambda.html#4524" class="Function">two</a> <a id="26832" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="26834" href="plfa.part2.Lambda.html#4524" class="Function">two</a>
  <a id="26840" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23259" class="InductiveConstructor Operator">—→⟨</a> <a id="26844" href="plfa.part2.Lambda.html#20229" class="InductiveConstructor">ξ-·₁</a> <a id="26849" class="Symbol">(</a><a id="26850" href="plfa.part2.Lambda.html#20405" class="InductiveConstructor">β-ƛ</a> <a id="26854" class="Symbol">(</a><a id="26855" href="plfa.part2.Lambda.html#12308" class="InductiveConstructor">V-suc</a> <a id="26861" class="Symbol">(</a><a id="26862" href="plfa.part2.Lambda.html#12308" class="InductiveConstructor">V-suc</a> <a id="26868" href="plfa.part2.Lambda.html#12260" class="InductiveConstructor">V-zero</a><a id="26874" class="Symbol">)))</a> <a id="26878" href="plfa.part2.Lambda.html#23259" class="InductiveConstructor Operator">⟩</a>
    <a id="26884" class="Symbol">(</a><a id="26885" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3854" class="InductiveConstructor Operator">ƛ</a> <a id="26887" class="String">&quot;n&quot;</a> <a id="26891" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a>
      <a id="26899" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#4023" class="InductiveConstructor Operator">case</a> <a id="26904" href="plfa.part2.Lambda.html#4524" class="Function">two</a> <a id="26908" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">[zero⇒</a> <a id="26915" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="26917" class="String">&quot;n&quot;</a> <a id="26921" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">|suc</a> <a id="26926" class="String">&quot;m&quot;</a> <a id="26930" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">⇒</a> <a id="26932" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="26937" class="Symbol">(</a><a id="26938" href="plfa.part2.Lambda.html#4558" class="Function">plus</a> <a id="26943" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="26945" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="26947" class="String">&quot;m&quot;</a> <a id="26951" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="26953" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="26955" class="String">&quot;n&quot;</a><a id="26958" class="Symbol">)</a> <a id="26960" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">]</a><a id="26961" class="Symbol">)</a>
         <a id="26972" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3900" class="InductiveConstructor Operator">·</a> <a id="26974" href="plfa.part2.Lambda.html#4524" class="Function">two</a>
  <a id="26980" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23259" class="InductiveConstructor Operator">—→⟨</a> <a id="26984" href="plfa.part2.Lambda.html#20405" class="InductiveConstructor">β-ƛ</a> <a id="26988" class="Symbol">(</a><a id="26989" href="plfa.part2.Lambda.html#12308" class="InductiveConstructor">V-suc</a> <a id="26995" class="Symbol">(</a><a id="26996" href="plfa.part2.Lambda.html#12308" class="InductiveConstructor">V-suc</a> <a id="27002" href="plfa.part2.Lambda.html#12260" class="InductiveConstructor">V-zero</a><a id="27008" class="Symbol">))</a> <a id="27011" href="plfa.part2.Lambda.html#23259" class="InductiveConstructor Operator">⟩</a>
    <a id="27017" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#4023" class="InductiveConstructor Operator">case</a> <a id="27022" href="plfa.part2.Lambda.html#4524" class="Function">two</a> <a id="27026" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">[zero⇒</a> <a id="27033" href="plfa.part2.Lambda.html#4524" class="Function">two</a> <a id="27037" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">|suc</a> <a id="27042" class="String">&quot;m&quot;</a> <a id="27046" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">⇒</a> <a id="27048" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="27053" class="Symbol">(</a><a id="27054" href="plfa.part2.Lambda.html#4558" class="Function">plus</a> <a id="27059" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="27061" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="27063" class="String">&quot;m&quot;</a> <a id="27067" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="27069" href="plfa.part2.Lambda.html#4524" class="Function">two</a><a id="27072" class="Symbol">)</a> <a id="27074" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">]</a>
  <a id="27078" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23259" class="InductiveConstructor Operator">—→⟨</a> <a id="27082" href="plfa.part2.Lambda.html#20888" class="InductiveConstructor">β-suc</a> <a id="27088" class="Symbol">(</a><a id="27089" href="plfa.part2.Lambda.html#12308" class="InductiveConstructor">V-suc</a> <a id="27095" href="plfa.part2.Lambda.html#12260" class="InductiveConstructor">V-zero</a><a id="27101" class="Symbol">)</a> <a id="27103" href="plfa.part2.Lambda.html#23259" class="InductiveConstructor Operator">⟩</a>
    <a id="27109" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3982" class="InductiveConstructor Operator">`suc</a> <a id="27114" class="Symbol">(</a><a id="27115" href="plfa.part2.Lambda.html#4558" class="Function">plus</a> <a id="27120" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="27122" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="27127" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a> <a id="27133" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="27135" href="plfa.part2.Lambda.html#4524" class="Function">two</a><a id="27138" class="Symbol">)</a>
  <a id="27142" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23259" class="InductiveConstructor Operator">—→⟨</a> <a id="27146" href="plfa.part2.Lambda.html#20511" class="InductiveConstructor">ξ-suc</a> <a id="27152" class="Symbol">(</a><a id="27153" href="plfa.part2.Lambda.html#20229" class="InductiveConstructor">ξ-·₁</a> <a id="27158" class="Symbol">(</a><a id="27159" href="plfa.part2.Lambda.html#20229" class="InductiveConstructor">ξ-·₁</a> <a id="27164" href="plfa.part2.Lambda.html#21039" class="InductiveConstructor">β-μ</a><a id="27167" class="Symbol">))</a> <a id="27170" href="plfa.part2.Lambda.html#23259" class="InductiveConstructor Operator">⟩</a>
    <a id="27176" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3982" class="InductiveConstructor Operator">`suc</a> <a id="27181" class="Symbol">((</a><a id="27183" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">ƛ</a> <a id="27185" class="String">&quot;m&quot;</a> <a id="27189" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a> <a id="27191" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">ƛ</a> <a id="27193" class="String">&quot;n&quot;</a> <a id="27197" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a>
      <a id="27205" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#4023" class="InductiveConstructor Operator">case</a> <a id="27210" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="27212" class="String">&quot;m&quot;</a> <a id="27216" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">[zero⇒</a> <a id="27223" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="27225" class="String">&quot;n&quot;</a> <a id="27229" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">|suc</a> <a id="27234" class="String">&quot;m&quot;</a> <a id="27238" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">⇒</a> <a id="27240" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="27245" class="Symbol">(</a><a id="27246" href="plfa.part2.Lambda.html#4558" class="Function">plus</a> <a id="27251" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="27253" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="27255" class="String">&quot;m&quot;</a> <a id="27259" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="27261" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="27263" class="String">&quot;n&quot;</a><a id="27266" class="Symbol">)</a> <a id="27268" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">]</a><a id="27269" class="Symbol">)</a>
        <a id="27279" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3900" class="InductiveConstructor Operator">·</a> <a id="27281" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="27286" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a> <a id="27292" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="27294" href="plfa.part2.Lambda.html#4524" class="Function">two</a><a id="27297" class="Symbol">)</a>
  <a id="27301" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23259" class="InductiveConstructor Operator">—→⟨</a> <a id="27305" href="plfa.part2.Lambda.html#20511" class="InductiveConstructor">ξ-suc</a> <a id="27311" class="Symbol">(</a><a id="27312" href="plfa.part2.Lambda.html#20229" class="InductiveConstructor">ξ-·₁</a> <a id="27317" class="Symbol">(</a><a id="27318" href="plfa.part2.Lambda.html#20405" class="InductiveConstructor">β-ƛ</a> <a id="27322" class="Symbol">(</a><a id="27323" href="plfa.part2.Lambda.html#12308" class="InductiveConstructor">V-suc</a> <a id="27329" href="plfa.part2.Lambda.html#12260" class="InductiveConstructor">V-zero</a><a id="27335" class="Symbol">)))</a> <a id="27339" href="plfa.part2.Lambda.html#23259" class="InductiveConstructor Operator">⟩</a>
    <a id="27345" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3982" class="InductiveConstructor Operator">`suc</a> <a id="27350" class="Symbol">((</a><a id="27352" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">ƛ</a> <a id="27354" class="String">&quot;n&quot;</a> <a id="27358" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a>
      <a id="27366" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#4023" class="InductiveConstructor Operator">case</a> <a id="27371" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="27376" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a> <a id="27382" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">[zero⇒</a> <a id="27389" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="27391" class="String">&quot;n&quot;</a> <a id="27395" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">|suc</a> <a id="27400" class="String">&quot;m&quot;</a> <a id="27404" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">⇒</a> <a id="27406" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="27411" class="Symbol">(</a><a id="27412" href="plfa.part2.Lambda.html#4558" class="Function">plus</a> <a id="27417" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="27419" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="27421" class="String">&quot;m&quot;</a> <a id="27425" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="27427" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="27429" class="String">&quot;n&quot;</a><a id="27432" class="Symbol">)</a> <a id="27434" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">]</a><a id="27435" class="Symbol">)</a>
        <a id="27445" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3900" class="InductiveConstructor Operator">·</a> <a id="27447" href="plfa.part2.Lambda.html#4524" class="Function">two</a><a id="27450" class="Symbol">)</a>
  <a id="27454" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23259" class="InductiveConstructor Operator">—→⟨</a> <a id="27458" href="plfa.part2.Lambda.html#20511" class="InductiveConstructor">ξ-suc</a> <a id="27464" class="Symbol">(</a><a id="27465" href="plfa.part2.Lambda.html#20405" class="InductiveConstructor">β-ƛ</a> <a id="27469" class="Symbol">(</a><a id="27470" href="plfa.part2.Lambda.html#12308" class="InductiveConstructor">V-suc</a> <a id="27476" class="Symbol">(</a><a id="27477" href="plfa.part2.Lambda.html#12308" class="InductiveConstructor">V-suc</a> <a id="27483" href="plfa.part2.Lambda.html#12260" class="InductiveConstructor">V-zero</a><a id="27489" class="Symbol">)))</a> <a id="27493" href="plfa.part2.Lambda.html#23259" class="InductiveConstructor Operator">⟩</a>
    <a id="27499" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3982" class="InductiveConstructor Operator">`suc</a> <a id="27504" class="Symbol">(</a><a id="27505" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">case</a> <a id="27510" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="27515" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a> <a id="27521" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">[zero⇒</a> <a id="27528" href="plfa.part2.Lambda.html#4524" class="Function">two</a> <a id="27532" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">|suc</a> <a id="27537" class="String">&quot;m&quot;</a> <a id="27541" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">⇒</a> <a id="27543" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="27548" class="Symbol">(</a><a id="27549" href="plfa.part2.Lambda.html#4558" class="Function">plus</a> <a id="27554" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="27556" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="27558" class="String">&quot;m&quot;</a> <a id="27562" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="27564" href="plfa.part2.Lambda.html#4524" class="Function">two</a><a id="27567" class="Symbol">)</a> <a id="27569" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">]</a><a id="27570" class="Symbol">)</a>
  <a id="27574" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23259" class="InductiveConstructor Operator">—→⟨</a> <a id="27578" href="plfa.part2.Lambda.html#20511" class="InductiveConstructor">ξ-suc</a> <a id="27584" class="Symbol">(</a><a id="27585" href="plfa.part2.Lambda.html#20888" class="InductiveConstructor">β-suc</a> <a id="27591" href="plfa.part2.Lambda.html#12260" class="InductiveConstructor">V-zero</a><a id="27597" class="Symbol">)</a> <a id="27599" href="plfa.part2.Lambda.html#23259" class="InductiveConstructor Operator">⟩</a>
    <a id="27605" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3982" class="InductiveConstructor Operator">`suc</a> <a id="27610" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="27615" class="Symbol">(</a><a id="27616" href="plfa.part2.Lambda.html#4558" class="Function">plus</a> <a id="27621" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="27623" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a> <a id="27629" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="27631" href="plfa.part2.Lambda.html#4524" class="Function">two</a><a id="27634" class="Symbol">)</a>
  <a id="27638" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23259" class="InductiveConstructor Operator">—→⟨</a> <a id="27642" href="plfa.part2.Lambda.html#20511" class="InductiveConstructor">ξ-suc</a> <a id="27648" class="Symbol">(</a><a id="27649" href="plfa.part2.Lambda.html#20511" class="InductiveConstructor">ξ-suc</a> <a id="27655" class="Symbol">(</a><a id="27656" href="plfa.part2.Lambda.html#20229" class="InductiveConstructor">ξ-·₁</a> <a id="27661" class="Symbol">(</a><a id="27662" href="plfa.part2.Lambda.html#20229" class="InductiveConstructor">ξ-·₁</a> <a id="27667" href="plfa.part2.Lambda.html#21039" class="InductiveConstructor">β-μ</a><a id="27670" class="Symbol">)))</a> <a id="27674" href="plfa.part2.Lambda.html#23259" class="InductiveConstructor Operator">⟩</a>
    <a id="27680" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3982" class="InductiveConstructor Operator">`suc</a> <a id="27685" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="27690" class="Symbol">((</a><a id="27692" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">ƛ</a> <a id="27694" class="String">&quot;m&quot;</a> <a id="27698" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a> <a id="27700" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">ƛ</a> <a id="27702" class="String">&quot;n&quot;</a> <a id="27706" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a>
      <a id="27714" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#4023" class="InductiveConstructor Operator">case</a> <a id="27719" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="27721" class="String">&quot;m&quot;</a> <a id="27725" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">[zero⇒</a> <a id="27732" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="27734" class="String">&quot;n&quot;</a> <a id="27738" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">|suc</a> <a id="27743" class="String">&quot;m&quot;</a> <a id="27747" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">⇒</a> <a id="27749" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="27754" class="Symbol">(</a><a id="27755" href="plfa.part2.Lambda.html#4558" class="Function">plus</a> <a id="27760" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="27762" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="27764" class="String">&quot;m&quot;</a> <a id="27768" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="27770" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="27772" class="String">&quot;n&quot;</a><a id="27775" class="Symbol">)</a> <a id="27777" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">]</a><a id="27778" class="Symbol">)</a>
        <a id="27788" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3900" class="InductiveConstructor Operator">·</a> <a id="27790" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a> <a id="27796" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="27798" href="plfa.part2.Lambda.html#4524" class="Function">two</a><a id="27801" class="Symbol">)</a>
  <a id="27805" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23259" class="InductiveConstructor Operator">—→⟨</a> <a id="27809" href="plfa.part2.Lambda.html#20511" class="InductiveConstructor">ξ-suc</a> <a id="27815" class="Symbol">(</a><a id="27816" href="plfa.part2.Lambda.html#20511" class="InductiveConstructor">ξ-suc</a> <a id="27822" class="Symbol">(</a><a id="27823" href="plfa.part2.Lambda.html#20229" class="InductiveConstructor">ξ-·₁</a> <a id="27828" class="Symbol">(</a><a id="27829" href="plfa.part2.Lambda.html#20405" class="InductiveConstructor">β-ƛ</a> <a id="27833" href="plfa.part2.Lambda.html#12260" class="InductiveConstructor">V-zero</a><a id="27839" class="Symbol">)))</a> <a id="27843" href="plfa.part2.Lambda.html#23259" class="InductiveConstructor Operator">⟩</a>
    <a id="27849" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3982" class="InductiveConstructor Operator">`suc</a> <a id="27854" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="27859" class="Symbol">((</a><a id="27861" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">ƛ</a> <a id="27863" class="String">&quot;n&quot;</a> <a id="27867" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a>
      <a id="27875" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#4023" class="InductiveConstructor Operator">case</a> <a id="27880" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a> <a id="27886" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">[zero⇒</a> <a id="27893" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="27895" class="String">&quot;n&quot;</a> <a id="27899" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">|suc</a> <a id="27904" class="String">&quot;m&quot;</a> <a id="27908" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">⇒</a> <a id="27910" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="27915" class="Symbol">(</a><a id="27916" href="plfa.part2.Lambda.html#4558" class="Function">plus</a> <a id="27921" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="27923" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="27925" class="String">&quot;m&quot;</a> <a id="27929" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="27931" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="27933" class="String">&quot;n&quot;</a><a id="27936" class="Symbol">)</a> <a id="27938" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">]</a><a id="27939" class="Symbol">)</a>
        <a id="27949" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3900" class="InductiveConstructor Operator">·</a> <a id="27951" href="plfa.part2.Lambda.html#4524" class="Function">two</a><a id="27954" class="Symbol">)</a>
  <a id="27958" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23259" class="InductiveConstructor Operator">—→⟨</a> <a id="27962" href="plfa.part2.Lambda.html#20511" class="InductiveConstructor">ξ-suc</a> <a id="27968" class="Symbol">(</a><a id="27969" href="plfa.part2.Lambda.html#20511" class="InductiveConstructor">ξ-suc</a> <a id="27975" class="Symbol">(</a><a id="27976" href="plfa.part2.Lambda.html#20405" class="InductiveConstructor">β-ƛ</a> <a id="27980" class="Symbol">(</a><a id="27981" href="plfa.part2.Lambda.html#12308" class="InductiveConstructor">V-suc</a> <a id="27987" class="Symbol">(</a><a id="27988" href="plfa.part2.Lambda.html#12308" class="InductiveConstructor">V-suc</a> <a id="27994" href="plfa.part2.Lambda.html#12260" class="InductiveConstructor">V-zero</a><a id="28000" class="Symbol">))))</a> <a id="28005" href="plfa.part2.Lambda.html#23259" class="InductiveConstructor Operator">⟩</a>
    <a id="28011" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3982" class="InductiveConstructor Operator">`suc</a> <a id="28016" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="28021" class="Symbol">(</a><a id="28022" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">case</a> <a id="28027" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a> <a id="28033" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">[zero⇒</a> <a id="28040" href="plfa.part2.Lambda.html#4524" class="Function">two</a> <a id="28044" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">|suc</a> <a id="28049" class="String">&quot;m&quot;</a> <a id="28053" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">⇒</a> <a id="28055" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="28060" class="Symbol">(</a><a id="28061" href="plfa.part2.Lambda.html#4558" class="Function">plus</a> <a id="28066" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="28068" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="28070" class="String">&quot;m&quot;</a> <a id="28074" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="28076" href="plfa.part2.Lambda.html#4524" class="Function">two</a><a id="28079" class="Symbol">)</a> <a id="28081" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">]</a><a id="28082" class="Symbol">)</a>
  <a id="28086" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23259" class="InductiveConstructor Operator">—→⟨</a> <a id="28090" href="plfa.part2.Lambda.html#20511" class="InductiveConstructor">ξ-suc</a> <a id="28096" class="Symbol">(</a><a id="28097" href="plfa.part2.Lambda.html#20511" class="InductiveConstructor">ξ-suc</a> <a id="28103" href="plfa.part2.Lambda.html#20775" class="InductiveConstructor">β-zero</a><a id="28109" class="Symbol">)</a> <a id="28111" href="plfa.part2.Lambda.html#23259" class="InductiveConstructor Operator">⟩</a>
    <a id="28117" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3982" class="InductiveConstructor Operator">`suc</a> <a id="28122" class="Symbol">(</a><a id="28123" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="28128" class="Symbol">(</a><a id="28129" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="28134" class="Symbol">(</a><a id="28135" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="28140" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a><a id="28145" class="Symbol">)))</a>
  <a id="28151" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23218" class="InductiveConstructor Operator">∎</a>
</pre>{% endraw %}
And here is a similar sample reduction for Church numerals:
{% raw %}<pre class="Agda"><a id="28222" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#28222" class="Function">_</a> <a id="28224" class="Symbol">:</a> <a id="28226" href="plfa.part2.Lambda.html#5834" class="Function">plusᶜ</a> <a id="28232" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="28234" href="plfa.part2.Lambda.html#5773" class="Function">twoᶜ</a> <a id="28239" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="28241" href="plfa.part2.Lambda.html#5773" class="Function">twoᶜ</a> <a id="28246" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="28248" href="plfa.part2.Lambda.html#5938" class="Function">sucᶜ</a> <a id="28253" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="28255" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a> <a id="28261" href="plfa.part2.Lambda.html#23185" class="Datatype Operator">—↠</a> <a id="28264" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="28269" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="28274" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="28279" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="28284" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a>
<a id="28290" class="Symbol">_</a> <a id="28292" class="Symbol">=</a>
  <a id="28296" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23335" class="Function Operator">begin</a>
    <a id="28306" class="Symbol">(</a><a id="28307" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3854" class="InductiveConstructor Operator">ƛ</a> <a id="28309" class="String">&quot;m&quot;</a> <a id="28313" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a> <a id="28315" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">ƛ</a> <a id="28317" class="String">&quot;n&quot;</a> <a id="28321" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a> <a id="28323" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">ƛ</a> <a id="28325" class="String">&quot;s&quot;</a> <a id="28329" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a> <a id="28331" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">ƛ</a> <a id="28333" class="String">&quot;z&quot;</a> <a id="28337" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a> <a id="28339" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="28341" class="String">&quot;m&quot;</a> <a id="28345" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="28347" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="28349" class="String">&quot;s&quot;</a> <a id="28353" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="28355" class="Symbol">(</a><a id="28356" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="28358" class="String">&quot;n&quot;</a> <a id="28362" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="28364" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="28366" class="String">&quot;s&quot;</a> <a id="28370" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="28372" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="28374" class="String">&quot;z&quot;</a><a id="28377" class="Symbol">))</a>
      <a id="28386" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3900" class="InductiveConstructor Operator">·</a> <a id="28388" href="plfa.part2.Lambda.html#5773" class="Function">twoᶜ</a> <a id="28393" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="28395" href="plfa.part2.Lambda.html#5773" class="Function">twoᶜ</a> <a id="28400" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="28402" href="plfa.part2.Lambda.html#5938" class="Function">sucᶜ</a> <a id="28407" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="28409" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a>
  <a id="28417" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23259" class="InductiveConstructor Operator">—→⟨</a> <a id="28421" href="plfa.part2.Lambda.html#20229" class="InductiveConstructor">ξ-·₁</a> <a id="28426" class="Symbol">(</a><a id="28427" href="plfa.part2.Lambda.html#20229" class="InductiveConstructor">ξ-·₁</a> <a id="28432" class="Symbol">(</a><a id="28433" href="plfa.part2.Lambda.html#20229" class="InductiveConstructor">ξ-·₁</a> <a id="28438" class="Symbol">(</a><a id="28439" href="plfa.part2.Lambda.html#20405" class="InductiveConstructor">β-ƛ</a> <a id="28443" href="plfa.part2.Lambda.html#12199" class="InductiveConstructor">V-ƛ</a><a id="28446" class="Symbol">)))</a> <a id="28450" href="plfa.part2.Lambda.html#23259" class="InductiveConstructor Operator">⟩</a>
    <a id="28456" class="Symbol">(</a><a id="28457" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3854" class="InductiveConstructor Operator">ƛ</a> <a id="28459" class="String">&quot;n&quot;</a> <a id="28463" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a> <a id="28465" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">ƛ</a> <a id="28467" class="String">&quot;s&quot;</a> <a id="28471" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a> <a id="28473" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">ƛ</a> <a id="28475" class="String">&quot;z&quot;</a> <a id="28479" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a> <a id="28481" href="plfa.part2.Lambda.html#5773" class="Function">twoᶜ</a> <a id="28486" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="28488" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="28490" class="String">&quot;s&quot;</a> <a id="28494" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="28496" class="Symbol">(</a><a id="28497" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="28499" class="String">&quot;n&quot;</a> <a id="28503" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="28505" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="28507" class="String">&quot;s&quot;</a> <a id="28511" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="28513" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="28515" class="String">&quot;z&quot;</a><a id="28518" class="Symbol">))</a>
      <a id="28527" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3900" class="InductiveConstructor Operator">·</a> <a id="28529" href="plfa.part2.Lambda.html#5773" class="Function">twoᶜ</a> <a id="28534" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="28536" href="plfa.part2.Lambda.html#5938" class="Function">sucᶜ</a> <a id="28541" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="28543" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a>
  <a id="28551" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23259" class="InductiveConstructor Operator">—→⟨</a> <a id="28555" href="plfa.part2.Lambda.html#20229" class="InductiveConstructor">ξ-·₁</a> <a id="28560" class="Symbol">(</a><a id="28561" href="plfa.part2.Lambda.html#20229" class="InductiveConstructor">ξ-·₁</a> <a id="28566" class="Symbol">(</a><a id="28567" href="plfa.part2.Lambda.html#20405" class="InductiveConstructor">β-ƛ</a> <a id="28571" href="plfa.part2.Lambda.html#12199" class="InductiveConstructor">V-ƛ</a><a id="28574" class="Symbol">))</a> <a id="28577" href="plfa.part2.Lambda.html#23259" class="InductiveConstructor Operator">⟩</a>
    <a id="28583" class="Symbol">(</a><a id="28584" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3854" class="InductiveConstructor Operator">ƛ</a> <a id="28586" class="String">&quot;s&quot;</a> <a id="28590" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a> <a id="28592" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">ƛ</a> <a id="28594" class="String">&quot;z&quot;</a> <a id="28598" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a> <a id="28600" href="plfa.part2.Lambda.html#5773" class="Function">twoᶜ</a> <a id="28605" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="28607" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="28609" class="String">&quot;s&quot;</a> <a id="28613" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="28615" class="Symbol">(</a><a id="28616" href="plfa.part2.Lambda.html#5773" class="Function">twoᶜ</a> <a id="28621" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="28623" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="28625" class="String">&quot;s&quot;</a> <a id="28629" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="28631" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="28633" class="String">&quot;z&quot;</a><a id="28636" class="Symbol">))</a> <a id="28639" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="28641" href="plfa.part2.Lambda.html#5938" class="Function">sucᶜ</a> <a id="28646" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="28648" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a>
  <a id="28656" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23259" class="InductiveConstructor Operator">—→⟨</a> <a id="28660" href="plfa.part2.Lambda.html#20229" class="InductiveConstructor">ξ-·₁</a> <a id="28665" class="Symbol">(</a><a id="28666" href="plfa.part2.Lambda.html#20405" class="InductiveConstructor">β-ƛ</a> <a id="28670" href="plfa.part2.Lambda.html#12199" class="InductiveConstructor">V-ƛ</a><a id="28673" class="Symbol">)</a> <a id="28675" href="plfa.part2.Lambda.html#23259" class="InductiveConstructor Operator">⟩</a>
    <a id="28681" class="Symbol">(</a><a id="28682" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3854" class="InductiveConstructor Operator">ƛ</a> <a id="28684" class="String">&quot;z&quot;</a> <a id="28688" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a> <a id="28690" href="plfa.part2.Lambda.html#5773" class="Function">twoᶜ</a> <a id="28695" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="28697" href="plfa.part2.Lambda.html#5938" class="Function">sucᶜ</a> <a id="28702" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="28704" class="Symbol">(</a><a id="28705" href="plfa.part2.Lambda.html#5773" class="Function">twoᶜ</a> <a id="28710" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="28712" href="plfa.part2.Lambda.html#5938" class="Function">sucᶜ</a> <a id="28717" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="28719" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="28721" class="String">&quot;z&quot;</a><a id="28724" class="Symbol">))</a> <a id="28727" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="28729" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a>
  <a id="28737" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23259" class="InductiveConstructor Operator">—→⟨</a> <a id="28741" href="plfa.part2.Lambda.html#20405" class="InductiveConstructor">β-ƛ</a> <a id="28745" href="plfa.part2.Lambda.html#12260" class="InductiveConstructor">V-zero</a> <a id="28752" href="plfa.part2.Lambda.html#23259" class="InductiveConstructor Operator">⟩</a>
    <a id="28758" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#5773" class="Function">twoᶜ</a> <a id="28763" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="28765" href="plfa.part2.Lambda.html#5938" class="Function">sucᶜ</a> <a id="28770" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="28772" class="Symbol">(</a><a id="28773" href="plfa.part2.Lambda.html#5773" class="Function">twoᶜ</a> <a id="28778" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="28780" href="plfa.part2.Lambda.html#5938" class="Function">sucᶜ</a> <a id="28785" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="28787" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a><a id="28792" class="Symbol">)</a>
  <a id="28796" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23259" class="InductiveConstructor Operator">—→⟨</a> <a id="28800" href="plfa.part2.Lambda.html#20229" class="InductiveConstructor">ξ-·₁</a> <a id="28805" class="Symbol">(</a><a id="28806" href="plfa.part2.Lambda.html#20405" class="InductiveConstructor">β-ƛ</a> <a id="28810" href="plfa.part2.Lambda.html#12199" class="InductiveConstructor">V-ƛ</a><a id="28813" class="Symbol">)</a> <a id="28815" href="plfa.part2.Lambda.html#23259" class="InductiveConstructor Operator">⟩</a>
    <a id="28821" class="Symbol">(</a><a id="28822" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3854" class="InductiveConstructor Operator">ƛ</a> <a id="28824" class="String">&quot;z&quot;</a> <a id="28828" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a> <a id="28830" href="plfa.part2.Lambda.html#5938" class="Function">sucᶜ</a> <a id="28835" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="28837" class="Symbol">(</a><a id="28838" href="plfa.part2.Lambda.html#5938" class="Function">sucᶜ</a> <a id="28843" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="28845" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="28847" class="String">&quot;z&quot;</a><a id="28850" class="Symbol">))</a> <a id="28853" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="28855" class="Symbol">(</a><a id="28856" href="plfa.part2.Lambda.html#5773" class="Function">twoᶜ</a> <a id="28861" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="28863" href="plfa.part2.Lambda.html#5938" class="Function">sucᶜ</a> <a id="28868" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="28870" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a><a id="28875" class="Symbol">)</a>
  <a id="28879" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23259" class="InductiveConstructor Operator">—→⟨</a> <a id="28883" href="plfa.part2.Lambda.html#20310" class="InductiveConstructor">ξ-·₂</a> <a id="28888" href="plfa.part2.Lambda.html#12199" class="InductiveConstructor">V-ƛ</a> <a id="28892" class="Symbol">(</a><a id="28893" href="plfa.part2.Lambda.html#20229" class="InductiveConstructor">ξ-·₁</a> <a id="28898" class="Symbol">(</a><a id="28899" href="plfa.part2.Lambda.html#20405" class="InductiveConstructor">β-ƛ</a> <a id="28903" href="plfa.part2.Lambda.html#12199" class="InductiveConstructor">V-ƛ</a><a id="28906" class="Symbol">))</a> <a id="28909" href="plfa.part2.Lambda.html#23259" class="InductiveConstructor Operator">⟩</a>
    <a id="28915" class="Symbol">(</a><a id="28916" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3854" class="InductiveConstructor Operator">ƛ</a> <a id="28918" class="String">&quot;z&quot;</a> <a id="28922" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a> <a id="28924" href="plfa.part2.Lambda.html#5938" class="Function">sucᶜ</a> <a id="28929" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="28931" class="Symbol">(</a><a id="28932" href="plfa.part2.Lambda.html#5938" class="Function">sucᶜ</a> <a id="28937" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="28939" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="28941" class="String">&quot;z&quot;</a><a id="28944" class="Symbol">))</a> <a id="28947" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="28949" class="Symbol">((</a><a id="28951" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">ƛ</a> <a id="28953" class="String">&quot;z&quot;</a> <a id="28957" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a> <a id="28959" href="plfa.part2.Lambda.html#5938" class="Function">sucᶜ</a> <a id="28964" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="28966" class="Symbol">(</a><a id="28967" href="plfa.part2.Lambda.html#5938" class="Function">sucᶜ</a> <a id="28972" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="28974" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="28976" class="String">&quot;z&quot;</a><a id="28979" class="Symbol">))</a> <a id="28982" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="28984" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a><a id="28989" class="Symbol">)</a>
  <a id="28993" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23259" class="InductiveConstructor Operator">—→⟨</a> <a id="28997" href="plfa.part2.Lambda.html#20310" class="InductiveConstructor">ξ-·₂</a> <a id="29002" href="plfa.part2.Lambda.html#12199" class="InductiveConstructor">V-ƛ</a> <a id="29006" class="Symbol">(</a><a id="29007" href="plfa.part2.Lambda.html#20405" class="InductiveConstructor">β-ƛ</a> <a id="29011" href="plfa.part2.Lambda.html#12260" class="InductiveConstructor">V-zero</a><a id="29017" class="Symbol">)</a> <a id="29019" href="plfa.part2.Lambda.html#23259" class="InductiveConstructor Operator">⟩</a>
    <a id="29025" class="Symbol">(</a><a id="29026" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3854" class="InductiveConstructor Operator">ƛ</a> <a id="29028" class="String">&quot;z&quot;</a> <a id="29032" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a> <a id="29034" href="plfa.part2.Lambda.html#5938" class="Function">sucᶜ</a> <a id="29039" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="29041" class="Symbol">(</a><a id="29042" href="plfa.part2.Lambda.html#5938" class="Function">sucᶜ</a> <a id="29047" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="29049" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="29051" class="String">&quot;z&quot;</a><a id="29054" class="Symbol">))</a> <a id="29057" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="29059" class="Symbol">(</a><a id="29060" href="plfa.part2.Lambda.html#5938" class="Function">sucᶜ</a> <a id="29065" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="29067" class="Symbol">(</a><a id="29068" href="plfa.part2.Lambda.html#5938" class="Function">sucᶜ</a> <a id="29073" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="29075" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a><a id="29080" class="Symbol">))</a>
  <a id="29085" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23259" class="InductiveConstructor Operator">—→⟨</a> <a id="29089" href="plfa.part2.Lambda.html#20310" class="InductiveConstructor">ξ-·₂</a> <a id="29094" href="plfa.part2.Lambda.html#12199" class="InductiveConstructor">V-ƛ</a> <a id="29098" class="Symbol">(</a><a id="29099" href="plfa.part2.Lambda.html#20310" class="InductiveConstructor">ξ-·₂</a> <a id="29104" href="plfa.part2.Lambda.html#12199" class="InductiveConstructor">V-ƛ</a> <a id="29108" class="Symbol">(</a><a id="29109" href="plfa.part2.Lambda.html#20405" class="InductiveConstructor">β-ƛ</a> <a id="29113" href="plfa.part2.Lambda.html#12260" class="InductiveConstructor">V-zero</a><a id="29119" class="Symbol">))</a> <a id="29122" href="plfa.part2.Lambda.html#23259" class="InductiveConstructor Operator">⟩</a>
    <a id="29128" class="Symbol">(</a><a id="29129" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3854" class="InductiveConstructor Operator">ƛ</a> <a id="29131" class="String">&quot;z&quot;</a> <a id="29135" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a> <a id="29137" href="plfa.part2.Lambda.html#5938" class="Function">sucᶜ</a> <a id="29142" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="29144" class="Symbol">(</a><a id="29145" href="plfa.part2.Lambda.html#5938" class="Function">sucᶜ</a> <a id="29150" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="29152" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="29154" class="String">&quot;z&quot;</a><a id="29157" class="Symbol">))</a> <a id="29160" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="29162" class="Symbol">(</a><a id="29163" href="plfa.part2.Lambda.html#5938" class="Function">sucᶜ</a> <a id="29168" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="29170" class="Symbol">(</a><a id="29171" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="29176" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a><a id="29181" class="Symbol">))</a>
  <a id="29186" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23259" class="InductiveConstructor Operator">—→⟨</a> <a id="29190" href="plfa.part2.Lambda.html#20310" class="InductiveConstructor">ξ-·₂</a> <a id="29195" href="plfa.part2.Lambda.html#12199" class="InductiveConstructor">V-ƛ</a> <a id="29199" class="Symbol">(</a><a id="29200" href="plfa.part2.Lambda.html#20405" class="InductiveConstructor">β-ƛ</a> <a id="29204" class="Symbol">(</a><a id="29205" href="plfa.part2.Lambda.html#12308" class="InductiveConstructor">V-suc</a> <a id="29211" href="plfa.part2.Lambda.html#12260" class="InductiveConstructor">V-zero</a><a id="29217" class="Symbol">))</a> <a id="29220" href="plfa.part2.Lambda.html#23259" class="InductiveConstructor Operator">⟩</a>
    <a id="29226" class="Symbol">(</a><a id="29227" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3854" class="InductiveConstructor Operator">ƛ</a> <a id="29229" class="String">&quot;z&quot;</a> <a id="29233" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a> <a id="29235" href="plfa.part2.Lambda.html#5938" class="Function">sucᶜ</a> <a id="29240" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="29242" class="Symbol">(</a><a id="29243" href="plfa.part2.Lambda.html#5938" class="Function">sucᶜ</a> <a id="29248" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="29250" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="29252" class="String">&quot;z&quot;</a><a id="29255" class="Symbol">))</a> <a id="29258" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="29260" class="Symbol">(</a><a id="29261" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="29266" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="29271" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a><a id="29276" class="Symbol">)</a>
  <a id="29280" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23259" class="InductiveConstructor Operator">—→⟨</a> <a id="29284" href="plfa.part2.Lambda.html#20405" class="InductiveConstructor">β-ƛ</a> <a id="29288" class="Symbol">(</a><a id="29289" href="plfa.part2.Lambda.html#12308" class="InductiveConstructor">V-suc</a> <a id="29295" class="Symbol">(</a><a id="29296" href="plfa.part2.Lambda.html#12308" class="InductiveConstructor">V-suc</a> <a id="29302" href="plfa.part2.Lambda.html#12260" class="InductiveConstructor">V-zero</a><a id="29308" class="Symbol">))</a> <a id="29311" href="plfa.part2.Lambda.html#23259" class="InductiveConstructor Operator">⟩</a>
    <a id="29317" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#5938" class="Function">sucᶜ</a> <a id="29322" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="29324" class="Symbol">(</a><a id="29325" href="plfa.part2.Lambda.html#5938" class="Function">sucᶜ</a> <a id="29330" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="29332" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="29337" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="29342" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a><a id="29347" class="Symbol">)</a>
  <a id="29351" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23259" class="InductiveConstructor Operator">—→⟨</a> <a id="29355" href="plfa.part2.Lambda.html#20310" class="InductiveConstructor">ξ-·₂</a> <a id="29360" href="plfa.part2.Lambda.html#12199" class="InductiveConstructor">V-ƛ</a> <a id="29364" class="Symbol">(</a><a id="29365" href="plfa.part2.Lambda.html#20405" class="InductiveConstructor">β-ƛ</a> <a id="29369" class="Symbol">(</a><a id="29370" href="plfa.part2.Lambda.html#12308" class="InductiveConstructor">V-suc</a> <a id="29376" class="Symbol">(</a><a id="29377" href="plfa.part2.Lambda.html#12308" class="InductiveConstructor">V-suc</a> <a id="29383" href="plfa.part2.Lambda.html#12260" class="InductiveConstructor">V-zero</a><a id="29389" class="Symbol">)))</a> <a id="29393" href="plfa.part2.Lambda.html#23259" class="InductiveConstructor Operator">⟩</a>
    <a id="29399" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#5938" class="Function">sucᶜ</a> <a id="29404" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="29406" class="Symbol">(</a><a id="29407" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="29412" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="29417" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="29422" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a><a id="29427" class="Symbol">)</a>
  <a id="29431" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23259" class="InductiveConstructor Operator">—→⟨</a> <a id="29435" href="plfa.part2.Lambda.html#20405" class="InductiveConstructor">β-ƛ</a> <a id="29439" class="Symbol">(</a><a id="29440" href="plfa.part2.Lambda.html#12308" class="InductiveConstructor">V-suc</a> <a id="29446" class="Symbol">(</a><a id="29447" href="plfa.part2.Lambda.html#12308" class="InductiveConstructor">V-suc</a> <a id="29453" class="Symbol">(</a><a id="29454" href="plfa.part2.Lambda.html#12308" class="InductiveConstructor">V-suc</a> <a id="29460" href="plfa.part2.Lambda.html#12260" class="InductiveConstructor">V-zero</a><a id="29466" class="Symbol">)))</a> <a id="29470" href="plfa.part2.Lambda.html#23259" class="InductiveConstructor Operator">⟩</a>
   <a id="29475" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3982" class="InductiveConstructor Operator">`suc</a> <a id="29480" class="Symbol">(</a><a id="29481" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="29486" class="Symbol">(</a><a id="29487" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="29492" class="Symbol">(</a><a id="29493" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="29498" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a><a id="29503" class="Symbol">)))</a>
  <a id="29509" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23218" class="InductiveConstructor Operator">∎</a>
</pre>{% endraw %}
In the next chapter, we will see how to compute such reduction sequences.


#### Exercise `plus-example` (practice)

Write out the reduction sequence demonstrating that one plus one is two.

{% raw %}<pre class="Agda"><a id="29711" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}

## Syntax of types

We have just two types:

  * Functions, `A ⇒ B`
  * Naturals, `` `ℕ ``

As before, to avoid overlap we use variants of the names used by Agda.

Here is the syntax of types in BNF:

    A, B, C  ::=  A ⇒ B | `ℕ

And here it is formalised in Agda:

{% raw %}<pre class="Agda"><a id="30011" class="Keyword">infixr</a> <a id="30018" class="Number">7</a> <a id="30020" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#30049" class="InductiveConstructor Operator">_⇒_</a>

<a id="30025" class="Keyword">data</a> <a id="Type"></a><a id="30030" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#30030" class="Datatype">Type</a> <a id="30035" class="Symbol">:</a> <a id="30037" class="PrimitiveType">Set</a> <a id="30041" class="Keyword">where</a>
  <a id="Type._⇒_"></a><a id="30049" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#30049" class="InductiveConstructor Operator">_⇒_</a> <a id="30053" class="Symbol">:</a> <a id="30055" href="plfa.part2.Lambda.html#30030" class="Datatype">Type</a> <a id="30060" class="Symbol">→</a> <a id="30062" href="plfa.part2.Lambda.html#30030" class="Datatype">Type</a> <a id="30067" class="Symbol">→</a> <a id="30069" href="plfa.part2.Lambda.html#30030" class="Datatype">Type</a>
  <a id="Type.`ℕ"></a><a id="30076" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#30076" class="InductiveConstructor">`ℕ</a> <a id="30079" class="Symbol">:</a> <a id="30081" href="plfa.part2.Lambda.html#30030" class="Datatype">Type</a>
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

{% raw %}<pre class="Agda"><a id="31666" class="Keyword">infixl</a> <a id="31673" class="Number">5</a>  <a id="31676" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#31728" class="InductiveConstructor Operator">_,_⦂_</a>

<a id="31683" class="Keyword">data</a> <a id="Context"></a><a id="31688" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#31688" class="Datatype">Context</a> <a id="31696" class="Symbol">:</a> <a id="31698" class="PrimitiveType">Set</a> <a id="31702" class="Keyword">where</a>
  <a id="Context.∅"></a><a id="31710" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#31710" class="InductiveConstructor">∅</a>     <a id="31716" class="Symbol">:</a> <a id="31718" href="plfa.part2.Lambda.html#31688" class="Datatype">Context</a>
  <a id="Context._,_⦂_"></a><a id="31728" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#31728" class="InductiveConstructor Operator">_,_⦂_</a> <a id="31734" class="Symbol">:</a> <a id="31736" href="plfa.part2.Lambda.html#31688" class="Datatype">Context</a> <a id="31744" class="Symbol">→</a> <a id="31746" href="plfa.part2.Lambda.html#3695" class="Function">Id</a> <a id="31749" class="Symbol">→</a> <a id="31751" href="plfa.part2.Lambda.html#30030" class="Datatype">Type</a> <a id="31756" class="Symbol">→</a> <a id="31758" href="plfa.part2.Lambda.html#31688" class="Datatype">Context</a>
</pre>{% endraw %}

#### Exercise `Context-≃` (practice)

Show that `Context` is isomorphic to `List (Id × Type)`.
For instance, the isomorphism relates the context

    ∅ , "s" ⦂ `ℕ ⇒ `ℕ , "z" ⦂ `ℕ

to the list

    [ ⟨ "z" , `ℕ ⟩ , ⟨ "s" , `ℕ ⇒ `ℕ ⟩ ]

{% raw %}<pre class="Agda"><a id="32011" class="Comment">-- Your code goes here</a>
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
{% raw %}<pre class="Agda"><a id="32900" class="Keyword">infix</a>  <a id="32907" class="Number">4</a>  <a id="32910" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#32922" class="Datatype Operator">_∋_⦂_</a>

<a id="32917" class="Keyword">data</a> <a id="_∋_⦂_"></a><a id="32922" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#32922" class="Datatype Operator">_∋_⦂_</a> <a id="32928" class="Symbol">:</a> <a id="32930" href="plfa.part2.Lambda.html#31688" class="Datatype">Context</a> <a id="32938" class="Symbol">→</a> <a id="32940" href="plfa.part2.Lambda.html#3695" class="Function">Id</a> <a id="32943" class="Symbol">→</a> <a id="32945" href="plfa.part2.Lambda.html#30030" class="Datatype">Type</a> <a id="32950" class="Symbol">→</a> <a id="32952" class="PrimitiveType">Set</a> <a id="32956" class="Keyword">where</a>

  <a id="_∋_⦂_.Z"></a><a id="32965" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#32965" class="InductiveConstructor">Z</a> <a id="32967" class="Symbol">:</a> <a id="32969" class="Symbol">∀</a> <a id="32971" class="Symbol">{</a><a id="32972" href="plfa.part2.Lambda.html#32972" class="Bound">Γ</a> <a id="32974" href="plfa.part2.Lambda.html#32974" class="Bound">x</a> <a id="32976" href="plfa.part2.Lambda.html#32976" class="Bound">A</a><a id="32977" class="Symbol">}</a>
      <a id="32985" class="Comment">------------------</a>
    <a id="33008" class="Symbol">→</a> <a id="33010" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#32972" class="Bound">Γ</a> <a id="33012" href="plfa.part2.Lambda.html#31728" class="InductiveConstructor Operator">,</a> <a id="33014" href="plfa.part2.Lambda.html#32974" class="Bound">x</a> <a id="33016" href="plfa.part2.Lambda.html#31728" class="InductiveConstructor Operator">⦂</a> <a id="33018" href="plfa.part2.Lambda.html#32976" class="Bound">A</a> <a id="33020" href="plfa.part2.Lambda.html#32922" class="Datatype Operator">∋</a> <a id="33022" href="plfa.part2.Lambda.html#32974" class="Bound">x</a> <a id="33024" href="plfa.part2.Lambda.html#32922" class="Datatype Operator">⦂</a> <a id="33026" href="plfa.part2.Lambda.html#32976" class="Bound">A</a>

  <a id="_∋_⦂_.S"></a><a id="33031" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#33031" class="InductiveConstructor">S</a> <a id="33033" class="Symbol">:</a> <a id="33035" class="Symbol">∀</a> <a id="33037" class="Symbol">{</a><a id="33038" href="plfa.part2.Lambda.html#33038" class="Bound">Γ</a> <a id="33040" href="plfa.part2.Lambda.html#33040" class="Bound">x</a> <a id="33042" href="plfa.part2.Lambda.html#33042" class="Bound">y</a> <a id="33044" href="plfa.part2.Lambda.html#33044" class="Bound">A</a> <a id="33046" href="plfa.part2.Lambda.html#33046" class="Bound">B</a><a id="33047" class="Symbol">}</a>
    <a id="33053" class="Symbol">→</a> <a id="33055" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#33040" class="Bound">x</a> <a id="33057" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#799" class="Function Operator">≢</a> <a id="33059" href="plfa.part2.Lambda.html#33042" class="Bound">y</a>
    <a id="33065" class="Symbol">→</a> <a id="33067" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#33038" class="Bound">Γ</a> <a id="33069" href="plfa.part2.Lambda.html#32922" class="Datatype Operator">∋</a> <a id="33071" href="plfa.part2.Lambda.html#33040" class="Bound">x</a> <a id="33073" href="plfa.part2.Lambda.html#32922" class="Datatype Operator">⦂</a> <a id="33075" href="plfa.part2.Lambda.html#33044" class="Bound">A</a>
      <a id="33083" class="Comment">------------------</a>
    <a id="33106" class="Symbol">→</a> <a id="33108" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#33038" class="Bound">Γ</a> <a id="33110" href="plfa.part2.Lambda.html#31728" class="InductiveConstructor Operator">,</a> <a id="33112" href="plfa.part2.Lambda.html#33042" class="Bound">y</a> <a id="33114" href="plfa.part2.Lambda.html#31728" class="InductiveConstructor Operator">⦂</a> <a id="33116" href="plfa.part2.Lambda.html#33046" class="Bound">B</a> <a id="33118" href="plfa.part2.Lambda.html#32922" class="Datatype Operator">∋</a> <a id="33120" href="plfa.part2.Lambda.html#33040" class="Bound">x</a> <a id="33122" href="plfa.part2.Lambda.html#32922" class="Datatype Operator">⦂</a> <a id="33124" href="plfa.part2.Lambda.html#33044" class="Bound">A</a>
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
{% raw %}<pre class="Agda"><a id="34064" class="Keyword">infix</a>  <a id="34071" class="Number">4</a>  <a id="34074" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#34086" class="Datatype Operator">_⊢_⦂_</a>

<a id="34081" class="Keyword">data</a> <a id="_⊢_⦂_"></a><a id="34086" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#34086" class="Datatype Operator">_⊢_⦂_</a> <a id="34092" class="Symbol">:</a> <a id="34094" href="plfa.part2.Lambda.html#31688" class="Datatype">Context</a> <a id="34102" class="Symbol">→</a> <a id="34104" href="plfa.part2.Lambda.html#3796" class="Datatype">Term</a> <a id="34109" class="Symbol">→</a> <a id="34111" href="plfa.part2.Lambda.html#30030" class="Datatype">Type</a> <a id="34116" class="Symbol">→</a> <a id="34118" class="PrimitiveType">Set</a> <a id="34122" class="Keyword">where</a>

  <a id="34131" class="Comment">-- Axiom </a>
  <a id="_⊢_⦂_.⊢`"></a><a id="34143" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#34143" class="InductiveConstructor">⊢`</a> <a id="34146" class="Symbol">:</a> <a id="34148" class="Symbol">∀</a> <a id="34150" class="Symbol">{</a><a id="34151" href="plfa.part2.Lambda.html#34151" class="Bound">Γ</a> <a id="34153" href="plfa.part2.Lambda.html#34153" class="Bound">x</a> <a id="34155" href="plfa.part2.Lambda.html#34155" class="Bound">A</a><a id="34156" class="Symbol">}</a>
    <a id="34162" class="Symbol">→</a> <a id="34164" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#34151" class="Bound">Γ</a> <a id="34166" href="plfa.part2.Lambda.html#32922" class="Datatype Operator">∋</a> <a id="34168" href="plfa.part2.Lambda.html#34153" class="Bound">x</a> <a id="34170" href="plfa.part2.Lambda.html#32922" class="Datatype Operator">⦂</a> <a id="34172" href="plfa.part2.Lambda.html#34155" class="Bound">A</a>
      <a id="34180" class="Comment">-----------</a>
    <a id="34196" class="Symbol">→</a> <a id="34198" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#34151" class="Bound">Γ</a> <a id="34200" href="plfa.part2.Lambda.html#34086" class="Datatype Operator">⊢</a> <a id="34202" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="34204" href="plfa.part2.Lambda.html#34153" class="Bound">x</a> <a id="34206" href="plfa.part2.Lambda.html#34086" class="Datatype Operator">⦂</a> <a id="34208" href="plfa.part2.Lambda.html#34155" class="Bound">A</a>

  <a id="34213" class="Comment">-- ⇒-I </a>
  <a id="_⊢_⦂_.⊢ƛ"></a><a id="34223" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#34223" class="InductiveConstructor">⊢ƛ</a> <a id="34226" class="Symbol">:</a> <a id="34228" class="Symbol">∀</a> <a id="34230" class="Symbol">{</a><a id="34231" href="plfa.part2.Lambda.html#34231" class="Bound">Γ</a> <a id="34233" href="plfa.part2.Lambda.html#34233" class="Bound">x</a> <a id="34235" href="plfa.part2.Lambda.html#34235" class="Bound">N</a> <a id="34237" href="plfa.part2.Lambda.html#34237" class="Bound">A</a> <a id="34239" href="plfa.part2.Lambda.html#34239" class="Bound">B</a><a id="34240" class="Symbol">}</a>
    <a id="34246" class="Symbol">→</a> <a id="34248" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#34231" class="Bound">Γ</a> <a id="34250" href="plfa.part2.Lambda.html#31728" class="InductiveConstructor Operator">,</a> <a id="34252" href="plfa.part2.Lambda.html#34233" class="Bound">x</a> <a id="34254" href="plfa.part2.Lambda.html#31728" class="InductiveConstructor Operator">⦂</a> <a id="34256" href="plfa.part2.Lambda.html#34237" class="Bound">A</a> <a id="34258" href="plfa.part2.Lambda.html#34086" class="Datatype Operator">⊢</a> <a id="34260" href="plfa.part2.Lambda.html#34235" class="Bound">N</a> <a id="34262" href="plfa.part2.Lambda.html#34086" class="Datatype Operator">⦂</a> <a id="34264" href="plfa.part2.Lambda.html#34239" class="Bound">B</a>
      <a id="34272" class="Comment">-------------------</a>
    <a id="34296" class="Symbol">→</a> <a id="34298" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#34231" class="Bound">Γ</a> <a id="34300" href="plfa.part2.Lambda.html#34086" class="Datatype Operator">⊢</a> <a id="34302" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">ƛ</a> <a id="34304" href="plfa.part2.Lambda.html#34233" class="Bound">x</a> <a id="34306" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a> <a id="34308" href="plfa.part2.Lambda.html#34235" class="Bound">N</a> <a id="34310" href="plfa.part2.Lambda.html#34086" class="Datatype Operator">⦂</a> <a id="34312" href="plfa.part2.Lambda.html#34237" class="Bound">A</a> <a id="34314" href="plfa.part2.Lambda.html#30049" class="InductiveConstructor Operator">⇒</a> <a id="34316" href="plfa.part2.Lambda.html#34239" class="Bound">B</a>

  <a id="34321" class="Comment">-- ⇒-E</a>
  <a id="_⊢_⦂_._·_"></a><a id="34330" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#34330" class="InductiveConstructor Operator">_·_</a> <a id="34334" class="Symbol">:</a> <a id="34336" class="Symbol">∀</a> <a id="34338" class="Symbol">{</a><a id="34339" href="plfa.part2.Lambda.html#34339" class="Bound">Γ</a> <a id="34341" href="plfa.part2.Lambda.html#34341" class="Bound">L</a> <a id="34343" href="plfa.part2.Lambda.html#34343" class="Bound">M</a> <a id="34345" href="plfa.part2.Lambda.html#34345" class="Bound">A</a> <a id="34347" href="plfa.part2.Lambda.html#34347" class="Bound">B</a><a id="34348" class="Symbol">}</a>
    <a id="34354" class="Symbol">→</a> <a id="34356" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#34339" class="Bound">Γ</a> <a id="34358" href="plfa.part2.Lambda.html#34086" class="Datatype Operator">⊢</a> <a id="34360" href="plfa.part2.Lambda.html#34341" class="Bound">L</a> <a id="34362" href="plfa.part2.Lambda.html#34086" class="Datatype Operator">⦂</a> <a id="34364" href="plfa.part2.Lambda.html#34345" class="Bound">A</a> <a id="34366" href="plfa.part2.Lambda.html#30049" class="InductiveConstructor Operator">⇒</a> <a id="34368" href="plfa.part2.Lambda.html#34347" class="Bound">B</a>
    <a id="34374" class="Symbol">→</a> <a id="34376" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#34339" class="Bound">Γ</a> <a id="34378" href="plfa.part2.Lambda.html#34086" class="Datatype Operator">⊢</a> <a id="34380" href="plfa.part2.Lambda.html#34343" class="Bound">M</a> <a id="34382" href="plfa.part2.Lambda.html#34086" class="Datatype Operator">⦂</a> <a id="34384" href="plfa.part2.Lambda.html#34345" class="Bound">A</a>
      <a id="34392" class="Comment">-------------</a>
    <a id="34410" class="Symbol">→</a> <a id="34412" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#34339" class="Bound">Γ</a> <a id="34414" href="plfa.part2.Lambda.html#34086" class="Datatype Operator">⊢</a> <a id="34416" href="plfa.part2.Lambda.html#34341" class="Bound">L</a> <a id="34418" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="34420" href="plfa.part2.Lambda.html#34343" class="Bound">M</a> <a id="34422" href="plfa.part2.Lambda.html#34086" class="Datatype Operator">⦂</a> <a id="34424" href="plfa.part2.Lambda.html#34347" class="Bound">B</a>

  <a id="34429" class="Comment">-- ℕ-I₁</a>
  <a id="_⊢_⦂_.⊢zero"></a><a id="34439" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#34439" class="InductiveConstructor">⊢zero</a> <a id="34445" class="Symbol">:</a> <a id="34447" class="Symbol">∀</a> <a id="34449" class="Symbol">{</a><a id="34450" href="plfa.part2.Lambda.html#34450" class="Bound">Γ</a><a id="34451" class="Symbol">}</a>
      <a id="34459" class="Comment">--------------</a>
    <a id="34478" class="Symbol">→</a> <a id="34480" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#34450" class="Bound">Γ</a> <a id="34482" href="plfa.part2.Lambda.html#34086" class="Datatype Operator">⊢</a> <a id="34484" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a> <a id="34490" href="plfa.part2.Lambda.html#34086" class="Datatype Operator">⦂</a> <a id="34492" href="plfa.part2.Lambda.html#30076" class="InductiveConstructor">`ℕ</a>

  <a id="34498" class="Comment">-- ℕ-I₂</a>
  <a id="_⊢_⦂_.⊢suc"></a><a id="34508" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#34508" class="InductiveConstructor">⊢suc</a> <a id="34513" class="Symbol">:</a> <a id="34515" class="Symbol">∀</a> <a id="34517" class="Symbol">{</a><a id="34518" href="plfa.part2.Lambda.html#34518" class="Bound">Γ</a> <a id="34520" href="plfa.part2.Lambda.html#34520" class="Bound">M</a><a id="34521" class="Symbol">}</a>
    <a id="34527" class="Symbol">→</a> <a id="34529" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#34518" class="Bound">Γ</a> <a id="34531" href="plfa.part2.Lambda.html#34086" class="Datatype Operator">⊢</a> <a id="34533" href="plfa.part2.Lambda.html#34520" class="Bound">M</a> <a id="34535" href="plfa.part2.Lambda.html#34086" class="Datatype Operator">⦂</a> <a id="34537" href="plfa.part2.Lambda.html#30076" class="InductiveConstructor">`ℕ</a>
      <a id="34546" class="Comment">---------------</a>
    <a id="34566" class="Symbol">→</a> <a id="34568" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#34518" class="Bound">Γ</a> <a id="34570" href="plfa.part2.Lambda.html#34086" class="Datatype Operator">⊢</a> <a id="34572" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="34577" href="plfa.part2.Lambda.html#34520" class="Bound">M</a> <a id="34579" href="plfa.part2.Lambda.html#34086" class="Datatype Operator">⦂</a> <a id="34581" href="plfa.part2.Lambda.html#30076" class="InductiveConstructor">`ℕ</a>

  <a id="34587" class="Comment">-- ℕ-E</a>
  <a id="_⊢_⦂_.⊢case"></a><a id="34596" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#34596" class="InductiveConstructor">⊢case</a> <a id="34602" class="Symbol">:</a> <a id="34604" class="Symbol">∀</a> <a id="34606" class="Symbol">{</a><a id="34607" href="plfa.part2.Lambda.html#34607" class="Bound">Γ</a> <a id="34609" href="plfa.part2.Lambda.html#34609" class="Bound">L</a> <a id="34611" href="plfa.part2.Lambda.html#34611" class="Bound">M</a> <a id="34613" href="plfa.part2.Lambda.html#34613" class="Bound">x</a> <a id="34615" href="plfa.part2.Lambda.html#34615" class="Bound">N</a> <a id="34617" href="plfa.part2.Lambda.html#34617" class="Bound">A</a><a id="34618" class="Symbol">}</a>
    <a id="34624" class="Symbol">→</a> <a id="34626" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#34607" class="Bound">Γ</a> <a id="34628" href="plfa.part2.Lambda.html#34086" class="Datatype Operator">⊢</a> <a id="34630" href="plfa.part2.Lambda.html#34609" class="Bound">L</a> <a id="34632" href="plfa.part2.Lambda.html#34086" class="Datatype Operator">⦂</a> <a id="34634" href="plfa.part2.Lambda.html#30076" class="InductiveConstructor">`ℕ</a>
    <a id="34641" class="Symbol">→</a> <a id="34643" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#34607" class="Bound">Γ</a> <a id="34645" href="plfa.part2.Lambda.html#34086" class="Datatype Operator">⊢</a> <a id="34647" href="plfa.part2.Lambda.html#34611" class="Bound">M</a> <a id="34649" href="plfa.part2.Lambda.html#34086" class="Datatype Operator">⦂</a> <a id="34651" href="plfa.part2.Lambda.html#34617" class="Bound">A</a>
    <a id="34657" class="Symbol">→</a> <a id="34659" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#34607" class="Bound">Γ</a> <a id="34661" href="plfa.part2.Lambda.html#31728" class="InductiveConstructor Operator">,</a> <a id="34663" href="plfa.part2.Lambda.html#34613" class="Bound">x</a> <a id="34665" href="plfa.part2.Lambda.html#31728" class="InductiveConstructor Operator">⦂</a> <a id="34667" href="plfa.part2.Lambda.html#30076" class="InductiveConstructor">`ℕ</a> <a id="34670" href="plfa.part2.Lambda.html#34086" class="Datatype Operator">⊢</a> <a id="34672" href="plfa.part2.Lambda.html#34615" class="Bound">N</a> <a id="34674" href="plfa.part2.Lambda.html#34086" class="Datatype Operator">⦂</a> <a id="34676" href="plfa.part2.Lambda.html#34617" class="Bound">A</a>
      <a id="34684" class="Comment">-------------------------------------</a>
    <a id="34726" class="Symbol">→</a> <a id="34728" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#34607" class="Bound">Γ</a> <a id="34730" href="plfa.part2.Lambda.html#34086" class="Datatype Operator">⊢</a> <a id="34732" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">case</a> <a id="34737" href="plfa.part2.Lambda.html#34609" class="Bound">L</a> <a id="34739" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">[zero⇒</a> <a id="34746" href="plfa.part2.Lambda.html#34611" class="Bound">M</a> <a id="34748" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">|suc</a> <a id="34753" href="plfa.part2.Lambda.html#34613" class="Bound">x</a> <a id="34755" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">⇒</a> <a id="34757" href="plfa.part2.Lambda.html#34615" class="Bound">N</a> <a id="34759" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">]</a> <a id="34761" href="plfa.part2.Lambda.html#34086" class="Datatype Operator">⦂</a> <a id="34763" href="plfa.part2.Lambda.html#34617" class="Bound">A</a>

  <a id="_⊢_⦂_.⊢μ"></a><a id="34768" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#34768" class="InductiveConstructor">⊢μ</a> <a id="34771" class="Symbol">:</a> <a id="34773" class="Symbol">∀</a> <a id="34775" class="Symbol">{</a><a id="34776" href="plfa.part2.Lambda.html#34776" class="Bound">Γ</a> <a id="34778" href="plfa.part2.Lambda.html#34778" class="Bound">x</a> <a id="34780" href="plfa.part2.Lambda.html#34780" class="Bound">M</a> <a id="34782" href="plfa.part2.Lambda.html#34782" class="Bound">A</a><a id="34783" class="Symbol">}</a>
    <a id="34789" class="Symbol">→</a> <a id="34791" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#34776" class="Bound">Γ</a> <a id="34793" href="plfa.part2.Lambda.html#31728" class="InductiveConstructor Operator">,</a> <a id="34795" href="plfa.part2.Lambda.html#34778" class="Bound">x</a> <a id="34797" href="plfa.part2.Lambda.html#31728" class="InductiveConstructor Operator">⦂</a> <a id="34799" href="plfa.part2.Lambda.html#34782" class="Bound">A</a> <a id="34801" href="plfa.part2.Lambda.html#34086" class="Datatype Operator">⊢</a> <a id="34803" href="plfa.part2.Lambda.html#34780" class="Bound">M</a> <a id="34805" href="plfa.part2.Lambda.html#34086" class="Datatype Operator">⦂</a> <a id="34807" href="plfa.part2.Lambda.html#34782" class="Bound">A</a>
      <a id="34815" class="Comment">-----------------</a>
    <a id="34837" class="Symbol">→</a> <a id="34839" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#34776" class="Bound">Γ</a> <a id="34841" href="plfa.part2.Lambda.html#34086" class="Datatype Operator">⊢</a> <a id="34843" href="plfa.part2.Lambda.html#4083" class="InductiveConstructor Operator">μ</a> <a id="34845" href="plfa.part2.Lambda.html#34778" class="Bound">x</a> <a id="34847" href="plfa.part2.Lambda.html#4083" class="InductiveConstructor Operator">⇒</a> <a id="34849" href="plfa.part2.Lambda.html#34780" class="Bound">M</a> <a id="34851" href="plfa.part2.Lambda.html#34086" class="Datatype Operator">⦂</a> <a id="34853" href="plfa.part2.Lambda.html#34782" class="Bound">A</a>
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
{% raw %}<pre class="Agda"><a id="Ch"></a><a id="37337" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#37337" class="Function">Ch</a> <a id="37340" class="Symbol">:</a> <a id="37342" href="plfa.part2.Lambda.html#30030" class="Datatype">Type</a> <a id="37347" class="Symbol">→</a> <a id="37349" href="plfa.part2.Lambda.html#30030" class="Datatype">Type</a>
<a id="37354" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#37337" class="Function">Ch</a> <a id="37357" href="plfa.part2.Lambda.html#37357" class="Bound">A</a> <a id="37359" class="Symbol">=</a> <a id="37361" class="Symbol">(</a><a id="37362" href="plfa.part2.Lambda.html#37357" class="Bound">A</a> <a id="37364" href="plfa.part2.Lambda.html#30049" class="InductiveConstructor Operator">⇒</a> <a id="37366" href="plfa.part2.Lambda.html#37357" class="Bound">A</a><a id="37367" class="Symbol">)</a> <a id="37369" href="plfa.part2.Lambda.html#30049" class="InductiveConstructor Operator">⇒</a> <a id="37371" href="plfa.part2.Lambda.html#37357" class="Bound">A</a> <a id="37373" href="plfa.part2.Lambda.html#30049" class="InductiveConstructor Operator">⇒</a> <a id="37375" href="plfa.part2.Lambda.html#37357" class="Bound">A</a>

<a id="⊢twoᶜ"></a><a id="37378" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#37378" class="Function">⊢twoᶜ</a> <a id="37384" class="Symbol">:</a> <a id="37386" class="Symbol">∀</a> <a id="37388" class="Symbol">{</a><a id="37389" href="plfa.part2.Lambda.html#37389" class="Bound">Γ</a> <a id="37391" href="plfa.part2.Lambda.html#37391" class="Bound">A</a><a id="37392" class="Symbol">}</a> <a id="37394" class="Symbol">→</a> <a id="37396" href="plfa.part2.Lambda.html#37389" class="Bound">Γ</a> <a id="37398" href="plfa.part2.Lambda.html#34086" class="Datatype Operator">⊢</a> <a id="37400" href="plfa.part2.Lambda.html#5773" class="Function">twoᶜ</a> <a id="37405" href="plfa.part2.Lambda.html#34086" class="Datatype Operator">⦂</a> <a id="37407" href="plfa.part2.Lambda.html#37337" class="Function">Ch</a> <a id="37410" href="plfa.part2.Lambda.html#37391" class="Bound">A</a>
<a id="37412" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#37378" class="Function">⊢twoᶜ</a> <a id="37418" class="Symbol">=</a> <a id="37420" href="plfa.part2.Lambda.html#34223" class="InductiveConstructor">⊢ƛ</a> <a id="37423" class="Symbol">(</a><a id="37424" href="plfa.part2.Lambda.html#34223" class="InductiveConstructor">⊢ƛ</a> <a id="37427" class="Symbol">(</a><a id="37428" href="plfa.part2.Lambda.html#34143" class="InductiveConstructor">⊢`</a> <a id="37431" href="plfa.part2.Lambda.html#37464" class="Function">∋s</a> <a id="37434" href="plfa.part2.Lambda.html#34330" class="InductiveConstructor Operator">·</a> <a id="37436" class="Symbol">(</a><a id="37437" href="plfa.part2.Lambda.html#34143" class="InductiveConstructor">⊢`</a> <a id="37440" href="plfa.part2.Lambda.html#37464" class="Function">∋s</a> <a id="37443" href="plfa.part2.Lambda.html#34330" class="InductiveConstructor Operator">·</a> <a id="37445" href="plfa.part2.Lambda.html#34143" class="InductiveConstructor">⊢`</a> <a id="37448" href="plfa.part2.Lambda.html#37481" class="Function">∋z</a><a id="37450" class="Symbol">)))</a>
  <a id="37456" class="Keyword">where</a>
  <a id="37464" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#37464" class="Function">∋s</a> <a id="37467" class="Symbol">=</a> <a id="37469" href="plfa.part2.Lambda.html#33031" class="InductiveConstructor">S</a> <a id="37471" class="Symbol">(λ())</a> <a id="37477" href="plfa.part2.Lambda.html#32965" class="InductiveConstructor">Z</a>
  <a id="37481" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#37481" class="Function">∋z</a> <a id="37484" class="Symbol">=</a> <a id="37486" href="plfa.part2.Lambda.html#32965" class="InductiveConstructor">Z</a>
</pre>{% endraw %}
Here are the typings corresponding to computing two plus two:
{% raw %}<pre class="Agda"><a id="⊢two"></a><a id="37559" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#37559" class="Function">⊢two</a> <a id="37564" class="Symbol">:</a> <a id="37566" class="Symbol">∀</a> <a id="37568" class="Symbol">{</a><a id="37569" href="plfa.part2.Lambda.html#37569" class="Bound">Γ</a><a id="37570" class="Symbol">}</a> <a id="37572" class="Symbol">→</a> <a id="37574" href="plfa.part2.Lambda.html#37569" class="Bound">Γ</a> <a id="37576" href="plfa.part2.Lambda.html#34086" class="Datatype Operator">⊢</a> <a id="37578" href="plfa.part2.Lambda.html#4524" class="Function">two</a> <a id="37582" href="plfa.part2.Lambda.html#34086" class="Datatype Operator">⦂</a> <a id="37584" href="plfa.part2.Lambda.html#30076" class="InductiveConstructor">`ℕ</a>
<a id="37587" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#37559" class="Function">⊢two</a> <a id="37592" class="Symbol">=</a> <a id="37594" href="plfa.part2.Lambda.html#34508" class="InductiveConstructor">⊢suc</a> <a id="37599" class="Symbol">(</a><a id="37600" href="plfa.part2.Lambda.html#34508" class="InductiveConstructor">⊢suc</a> <a id="37605" href="plfa.part2.Lambda.html#34439" class="InductiveConstructor">⊢zero</a><a id="37610" class="Symbol">)</a>

<a id="⊢plus"></a><a id="37613" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#37613" class="Function">⊢plus</a> <a id="37619" class="Symbol">:</a> <a id="37621" class="Symbol">∀</a> <a id="37623" class="Symbol">{</a><a id="37624" href="plfa.part2.Lambda.html#37624" class="Bound">Γ</a><a id="37625" class="Symbol">}</a> <a id="37627" class="Symbol">→</a> <a id="37629" href="plfa.part2.Lambda.html#37624" class="Bound">Γ</a> <a id="37631" href="plfa.part2.Lambda.html#34086" class="Datatype Operator">⊢</a> <a id="37633" href="plfa.part2.Lambda.html#4558" class="Function">plus</a> <a id="37638" href="plfa.part2.Lambda.html#34086" class="Datatype Operator">⦂</a> <a id="37640" href="plfa.part2.Lambda.html#30076" class="InductiveConstructor">`ℕ</a> <a id="37643" href="plfa.part2.Lambda.html#30049" class="InductiveConstructor Operator">⇒</a> <a id="37645" href="plfa.part2.Lambda.html#30076" class="InductiveConstructor">`ℕ</a> <a id="37648" href="plfa.part2.Lambda.html#30049" class="InductiveConstructor Operator">⇒</a> <a id="37650" href="plfa.part2.Lambda.html#30076" class="InductiveConstructor">`ℕ</a>
<a id="37653" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#37613" class="Function">⊢plus</a> <a id="37659" class="Symbol">=</a> <a id="37661" href="plfa.part2.Lambda.html#34768" class="InductiveConstructor">⊢μ</a> <a id="37664" class="Symbol">(</a><a id="37665" href="plfa.part2.Lambda.html#34223" class="InductiveConstructor">⊢ƛ</a> <a id="37668" class="Symbol">(</a><a id="37669" href="plfa.part2.Lambda.html#34223" class="InductiveConstructor">⊢ƛ</a> <a id="37672" class="Symbol">(</a><a id="37673" href="plfa.part2.Lambda.html#34596" class="InductiveConstructor">⊢case</a> <a id="37679" class="Symbol">(</a><a id="37680" href="plfa.part2.Lambda.html#34143" class="InductiveConstructor">⊢`</a> <a id="37683" href="plfa.part2.Lambda.html#37790" class="Function">∋m</a><a id="37685" class="Symbol">)</a> <a id="37687" class="Symbol">(</a><a id="37688" href="plfa.part2.Lambda.html#34143" class="InductiveConstructor">⊢`</a> <a id="37691" href="plfa.part2.Lambda.html#37810" class="Function">∋n</a><a id="37693" class="Symbol">)</a>
         <a id="37704" class="Symbol">(</a><a id="37705" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#34508" class="InductiveConstructor">⊢suc</a> <a id="37710" class="Symbol">(</a><a id="37711" href="plfa.part2.Lambda.html#34143" class="InductiveConstructor">⊢`</a> <a id="37714" href="plfa.part2.Lambda.html#37750" class="Function">∋+</a> <a id="37717" href="plfa.part2.Lambda.html#34330" class="InductiveConstructor Operator">·</a> <a id="37719" href="plfa.part2.Lambda.html#34143" class="InductiveConstructor">⊢`</a> <a id="37722" href="plfa.part2.Lambda.html#37820" class="Function">∋m′</a> <a id="37726" href="plfa.part2.Lambda.html#34330" class="InductiveConstructor Operator">·</a> <a id="37728" href="plfa.part2.Lambda.html#34143" class="InductiveConstructor">⊢`</a> <a id="37731" href="plfa.part2.Lambda.html#37830" class="Function">∋n′</a><a id="37734" class="Symbol">)))))</a>
  <a id="37742" class="Keyword">where</a>
  <a id="37750" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#37750" class="Function">∋+</a>  <a id="37754" class="Symbol">=</a> <a id="37756" class="Symbol">(</a><a id="37757" href="plfa.part2.Lambda.html#33031" class="InductiveConstructor">S</a> <a id="37759" class="Symbol">(λ())</a> <a id="37765" class="Symbol">(</a><a id="37766" href="plfa.part2.Lambda.html#33031" class="InductiveConstructor">S</a> <a id="37768" class="Symbol">(λ())</a> <a id="37774" class="Symbol">(</a><a id="37775" href="plfa.part2.Lambda.html#33031" class="InductiveConstructor">S</a> <a id="37777" class="Symbol">(λ())</a> <a id="37783" href="plfa.part2.Lambda.html#32965" class="InductiveConstructor">Z</a><a id="37784" class="Symbol">)))</a>
  <a id="37790" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#37790" class="Function">∋m</a>  <a id="37794" class="Symbol">=</a> <a id="37796" class="Symbol">(</a><a id="37797" href="plfa.part2.Lambda.html#33031" class="InductiveConstructor">S</a> <a id="37799" class="Symbol">(λ())</a> <a id="37805" href="plfa.part2.Lambda.html#32965" class="InductiveConstructor">Z</a><a id="37806" class="Symbol">)</a>
  <a id="37810" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#37810" class="Function">∋n</a>  <a id="37814" class="Symbol">=</a> <a id="37816" href="plfa.part2.Lambda.html#32965" class="InductiveConstructor">Z</a>
  <a id="37820" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#37820" class="Function">∋m′</a> <a id="37824" class="Symbol">=</a> <a id="37826" href="plfa.part2.Lambda.html#32965" class="InductiveConstructor">Z</a>
  <a id="37830" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#37830" class="Function">∋n′</a> <a id="37834" class="Symbol">=</a> <a id="37836" class="Symbol">(</a><a id="37837" href="plfa.part2.Lambda.html#33031" class="InductiveConstructor">S</a> <a id="37839" class="Symbol">(λ())</a> <a id="37845" href="plfa.part2.Lambda.html#32965" class="InductiveConstructor">Z</a><a id="37846" class="Symbol">)</a>

<a id="⊢2+2"></a><a id="37849" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#37849" class="Function">⊢2+2</a> <a id="37854" class="Symbol">:</a> <a id="37856" href="plfa.part2.Lambda.html#31710" class="InductiveConstructor">∅</a> <a id="37858" href="plfa.part2.Lambda.html#34086" class="Datatype Operator">⊢</a> <a id="37860" href="plfa.part2.Lambda.html#4558" class="Function">plus</a> <a id="37865" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="37867" href="plfa.part2.Lambda.html#4524" class="Function">two</a> <a id="37871" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="37873" href="plfa.part2.Lambda.html#4524" class="Function">two</a> <a id="37877" href="plfa.part2.Lambda.html#34086" class="Datatype Operator">⦂</a> <a id="37879" href="plfa.part2.Lambda.html#30076" class="InductiveConstructor">`ℕ</a>
<a id="37882" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#37849" class="Function">⊢2+2</a> <a id="37887" class="Symbol">=</a> <a id="37889" href="plfa.part2.Lambda.html#37613" class="Function">⊢plus</a> <a id="37895" href="plfa.part2.Lambda.html#34330" class="InductiveConstructor Operator">·</a> <a id="37897" href="plfa.part2.Lambda.html#37559" class="Function">⊢two</a> <a id="37902" href="plfa.part2.Lambda.html#34330" class="InductiveConstructor Operator">·</a> <a id="37904" href="plfa.part2.Lambda.html#37559" class="Function">⊢two</a>
</pre>{% endraw %}In contrast to our earlier examples, here we have typed `two` and `plus`
in an arbitrary context rather than the empty context; this makes it easy
to use them inside other binding contexts as well as at the top level.
Here the two lookup judgments `∋m` and `∋m′` refer to two different
bindings of variables named `"m"`.  In contrast, the two judgments `∋n` and
`∋n′` both refer to the same binding of `"n"` but accessed in different
contexts, the first where "n" is the last binding in the context, and
the second after "m" is bound in the successor branch of the case.

And here are typings for the remainder of the Church example:
{% raw %}<pre class="Agda"><a id="⊢plusᶜ"></a><a id="38551" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#38551" class="Function">⊢plusᶜ</a> <a id="38558" class="Symbol">:</a> <a id="38560" class="Symbol">∀</a> <a id="38562" class="Symbol">{</a><a id="38563" href="plfa.part2.Lambda.html#38563" class="Bound">Γ</a> <a id="38565" href="plfa.part2.Lambda.html#38565" class="Bound">A</a><a id="38566" class="Symbol">}</a> <a id="38568" class="Symbol">→</a> <a id="38570" href="plfa.part2.Lambda.html#38563" class="Bound">Γ</a>  <a id="38573" href="plfa.part2.Lambda.html#34086" class="Datatype Operator">⊢</a> <a id="38575" href="plfa.part2.Lambda.html#5834" class="Function">plusᶜ</a> <a id="38581" href="plfa.part2.Lambda.html#34086" class="Datatype Operator">⦂</a> <a id="38583" href="plfa.part2.Lambda.html#37337" class="Function">Ch</a> <a id="38586" href="plfa.part2.Lambda.html#38565" class="Bound">A</a> <a id="38588" href="plfa.part2.Lambda.html#30049" class="InductiveConstructor Operator">⇒</a> <a id="38590" href="plfa.part2.Lambda.html#37337" class="Function">Ch</a> <a id="38593" href="plfa.part2.Lambda.html#38565" class="Bound">A</a> <a id="38595" href="plfa.part2.Lambda.html#30049" class="InductiveConstructor Operator">⇒</a> <a id="38597" href="plfa.part2.Lambda.html#37337" class="Function">Ch</a> <a id="38600" href="plfa.part2.Lambda.html#38565" class="Bound">A</a>
<a id="38602" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#38551" class="Function">⊢plusᶜ</a> <a id="38609" class="Symbol">=</a> <a id="38611" href="plfa.part2.Lambda.html#34223" class="InductiveConstructor">⊢ƛ</a> <a id="38614" class="Symbol">(</a><a id="38615" href="plfa.part2.Lambda.html#34223" class="InductiveConstructor">⊢ƛ</a> <a id="38618" class="Symbol">(</a><a id="38619" href="plfa.part2.Lambda.html#34223" class="InductiveConstructor">⊢ƛ</a> <a id="38622" class="Symbol">(</a><a id="38623" href="plfa.part2.Lambda.html#34223" class="InductiveConstructor">⊢ƛ</a> <a id="38626" class="Symbol">(</a><a id="38627" href="plfa.part2.Lambda.html#34143" class="InductiveConstructor">⊢`</a> <a id="38630" href="plfa.part2.Lambda.html#38681" class="Function">∋m</a> <a id="38633" href="plfa.part2.Lambda.html#34330" class="InductiveConstructor Operator">·</a> <a id="38635" href="plfa.part2.Lambda.html#34143" class="InductiveConstructor">⊢`</a> <a id="38638" href="plfa.part2.Lambda.html#38745" class="Function">∋s</a> <a id="38641" href="plfa.part2.Lambda.html#34330" class="InductiveConstructor Operator">·</a> <a id="38643" class="Symbol">(</a><a id="38644" href="plfa.part2.Lambda.html#34143" class="InductiveConstructor">⊢`</a> <a id="38647" href="plfa.part2.Lambda.html#38718" class="Function">∋n</a> <a id="38650" href="plfa.part2.Lambda.html#34330" class="InductiveConstructor Operator">·</a> <a id="38652" href="plfa.part2.Lambda.html#34143" class="InductiveConstructor">⊢`</a> <a id="38655" href="plfa.part2.Lambda.html#38745" class="Function">∋s</a> <a id="38658" href="plfa.part2.Lambda.html#34330" class="InductiveConstructor Operator">·</a> <a id="38660" href="plfa.part2.Lambda.html#34143" class="InductiveConstructor">⊢`</a> <a id="38663" href="plfa.part2.Lambda.html#38762" class="Function">∋z</a><a id="38665" class="Symbol">)))))</a>
  <a id="38673" class="Keyword">where</a>
  <a id="38681" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#38681" class="Function">∋m</a> <a id="38684" class="Symbol">=</a> <a id="38686" href="plfa.part2.Lambda.html#33031" class="InductiveConstructor">S</a> <a id="38688" class="Symbol">(λ())</a> <a id="38694" class="Symbol">(</a><a id="38695" href="plfa.part2.Lambda.html#33031" class="InductiveConstructor">S</a> <a id="38697" class="Symbol">(λ())</a> <a id="38703" class="Symbol">(</a><a id="38704" href="plfa.part2.Lambda.html#33031" class="InductiveConstructor">S</a> <a id="38706" class="Symbol">(λ())</a> <a id="38712" href="plfa.part2.Lambda.html#32965" class="InductiveConstructor">Z</a><a id="38713" class="Symbol">))</a>
  <a id="38718" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#38718" class="Function">∋n</a> <a id="38721" class="Symbol">=</a> <a id="38723" href="plfa.part2.Lambda.html#33031" class="InductiveConstructor">S</a> <a id="38725" class="Symbol">(λ())</a> <a id="38731" class="Symbol">(</a><a id="38732" href="plfa.part2.Lambda.html#33031" class="InductiveConstructor">S</a> <a id="38734" class="Symbol">(λ())</a> <a id="38740" href="plfa.part2.Lambda.html#32965" class="InductiveConstructor">Z</a><a id="38741" class="Symbol">)</a>
  <a id="38745" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#38745" class="Function">∋s</a> <a id="38748" class="Symbol">=</a> <a id="38750" href="plfa.part2.Lambda.html#33031" class="InductiveConstructor">S</a> <a id="38752" class="Symbol">(λ())</a> <a id="38758" href="plfa.part2.Lambda.html#32965" class="InductiveConstructor">Z</a>
  <a id="38762" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#38762" class="Function">∋z</a> <a id="38765" class="Symbol">=</a> <a id="38767" href="plfa.part2.Lambda.html#32965" class="InductiveConstructor">Z</a>

<a id="⊢sucᶜ"></a><a id="38770" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#38770" class="Function">⊢sucᶜ</a> <a id="38776" class="Symbol">:</a> <a id="38778" class="Symbol">∀</a> <a id="38780" class="Symbol">{</a><a id="38781" href="plfa.part2.Lambda.html#38781" class="Bound">Γ</a><a id="38782" class="Symbol">}</a> <a id="38784" class="Symbol">→</a> <a id="38786" href="plfa.part2.Lambda.html#38781" class="Bound">Γ</a> <a id="38788" href="plfa.part2.Lambda.html#34086" class="Datatype Operator">⊢</a> <a id="38790" href="plfa.part2.Lambda.html#5938" class="Function">sucᶜ</a> <a id="38795" href="plfa.part2.Lambda.html#34086" class="Datatype Operator">⦂</a> <a id="38797" href="plfa.part2.Lambda.html#30076" class="InductiveConstructor">`ℕ</a> <a id="38800" href="plfa.part2.Lambda.html#30049" class="InductiveConstructor Operator">⇒</a> <a id="38802" href="plfa.part2.Lambda.html#30076" class="InductiveConstructor">`ℕ</a>
<a id="38805" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#38770" class="Function">⊢sucᶜ</a> <a id="38811" class="Symbol">=</a> <a id="38813" href="plfa.part2.Lambda.html#34223" class="InductiveConstructor">⊢ƛ</a> <a id="38816" class="Symbol">(</a><a id="38817" href="plfa.part2.Lambda.html#34508" class="InductiveConstructor">⊢suc</a> <a id="38822" class="Symbol">(</a><a id="38823" href="plfa.part2.Lambda.html#34143" class="InductiveConstructor">⊢`</a> <a id="38826" href="plfa.part2.Lambda.html#38841" class="Function">∋n</a><a id="38828" class="Symbol">))</a>
  <a id="38833" class="Keyword">where</a>
  <a id="38841" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#38841" class="Function">∋n</a> <a id="38844" class="Symbol">=</a> <a id="38846" href="plfa.part2.Lambda.html#32965" class="InductiveConstructor">Z</a>

<a id="⊢2+2ᶜ"></a><a id="38849" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#38849" class="Function">⊢2+2ᶜ</a> <a id="38855" class="Symbol">:</a> <a id="38857" href="plfa.part2.Lambda.html#31710" class="InductiveConstructor">∅</a> <a id="38859" href="plfa.part2.Lambda.html#34086" class="Datatype Operator">⊢</a> <a id="38861" href="plfa.part2.Lambda.html#5834" class="Function">plusᶜ</a> <a id="38867" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="38869" href="plfa.part2.Lambda.html#5773" class="Function">twoᶜ</a> <a id="38874" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="38876" href="plfa.part2.Lambda.html#5773" class="Function">twoᶜ</a> <a id="38881" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="38883" href="plfa.part2.Lambda.html#5938" class="Function">sucᶜ</a> <a id="38888" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="38890" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a> <a id="38896" href="plfa.part2.Lambda.html#34086" class="Datatype Operator">⦂</a> <a id="38898" href="plfa.part2.Lambda.html#30076" class="InductiveConstructor">`ℕ</a>
<a id="38901" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#38849" class="Function">⊢2+2ᶜ</a> <a id="38907" class="Symbol">=</a> <a id="38909" href="plfa.part2.Lambda.html#38551" class="Function">⊢plusᶜ</a> <a id="38916" href="plfa.part2.Lambda.html#34330" class="InductiveConstructor Operator">·</a> <a id="38918" href="plfa.part2.Lambda.html#37378" class="Function">⊢twoᶜ</a> <a id="38924" href="plfa.part2.Lambda.html#34330" class="InductiveConstructor Operator">·</a> <a id="38926" href="plfa.part2.Lambda.html#37378" class="Function">⊢twoᶜ</a> <a id="38932" href="plfa.part2.Lambda.html#34330" class="InductiveConstructor Operator">·</a> <a id="38934" href="plfa.part2.Lambda.html#38770" class="Function">⊢sucᶜ</a> <a id="38940" href="plfa.part2.Lambda.html#34330" class="InductiveConstructor Operator">·</a> <a id="38942" href="plfa.part2.Lambda.html#34439" class="InductiveConstructor">⊢zero</a>
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
{% raw %}<pre class="Agda"><a id="∋-injective"></a><a id="40258" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#40258" class="Function">∋-injective</a> <a id="40270" class="Symbol">:</a> <a id="40272" class="Symbol">∀</a> <a id="40274" class="Symbol">{</a><a id="40275" href="plfa.part2.Lambda.html#40275" class="Bound">Γ</a> <a id="40277" href="plfa.part2.Lambda.html#40277" class="Bound">x</a> <a id="40279" href="plfa.part2.Lambda.html#40279" class="Bound">A</a> <a id="40281" href="plfa.part2.Lambda.html#40281" class="Bound">B</a><a id="40282" class="Symbol">}</a> <a id="40284" class="Symbol">→</a> <a id="40286" href="plfa.part2.Lambda.html#40275" class="Bound">Γ</a> <a id="40288" href="plfa.part2.Lambda.html#32922" class="Datatype Operator">∋</a> <a id="40290" href="plfa.part2.Lambda.html#40277" class="Bound">x</a> <a id="40292" href="plfa.part2.Lambda.html#32922" class="Datatype Operator">⦂</a> <a id="40294" href="plfa.part2.Lambda.html#40279" class="Bound">A</a> <a id="40296" class="Symbol">→</a> <a id="40298" href="plfa.part2.Lambda.html#40275" class="Bound">Γ</a> <a id="40300" href="plfa.part2.Lambda.html#32922" class="Datatype Operator">∋</a> <a id="40302" href="plfa.part2.Lambda.html#40277" class="Bound">x</a> <a id="40304" href="plfa.part2.Lambda.html#32922" class="Datatype Operator">⦂</a> <a id="40306" href="plfa.part2.Lambda.html#40281" class="Bound">B</a> <a id="40308" class="Symbol">→</a> <a id="40310" href="plfa.part2.Lambda.html#40279" class="Bound">A</a> <a id="40312" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="40314" href="plfa.part2.Lambda.html#40281" class="Bound">B</a>
<a id="40316" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#40258" class="Function">∋-injective</a> <a id="40328" href="plfa.part2.Lambda.html#32965" class="InductiveConstructor">Z</a>        <a id="40337" href="plfa.part2.Lambda.html#32965" class="InductiveConstructor">Z</a>          <a id="40348" class="Symbol">=</a>  <a id="40351" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>
<a id="40356" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#40258" class="Function">∋-injective</a> <a id="40368" href="plfa.part2.Lambda.html#32965" class="InductiveConstructor">Z</a>        <a id="40377" class="Symbol">(</a><a id="40378" href="plfa.part2.Lambda.html#33031" class="InductiveConstructor">S</a> <a id="40380" href="plfa.part2.Lambda.html#40380" class="Bound">x≢</a> <a id="40383" class="Symbol">_)</a>   <a id="40388" class="Symbol">=</a>  <a id="40391" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html#294" class="Function">⊥-elim</a> <a id="40398" class="Symbol">(</a><a id="40399" href="plfa.part2.Lambda.html#40380" class="Bound">x≢</a> <a id="40402" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a><a id="40406" class="Symbol">)</a>
<a id="40408" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#40258" class="Function">∋-injective</a> <a id="40420" class="Symbol">(</a><a id="40421" href="plfa.part2.Lambda.html#33031" class="InductiveConstructor">S</a> <a id="40423" href="plfa.part2.Lambda.html#40423" class="Bound">x≢</a> <a id="40426" class="Symbol">_)</a> <a id="40429" href="plfa.part2.Lambda.html#32965" class="InductiveConstructor">Z</a>          <a id="40440" class="Symbol">=</a>  <a id="40443" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html#294" class="Function">⊥-elim</a> <a id="40450" class="Symbol">(</a><a id="40451" href="plfa.part2.Lambda.html#40423" class="Bound">x≢</a> <a id="40454" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a><a id="40458" class="Symbol">)</a>
<a id="40460" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#40258" class="Function">∋-injective</a> <a id="40472" class="Symbol">(</a><a id="40473" href="plfa.part2.Lambda.html#33031" class="InductiveConstructor">S</a> <a id="40475" class="Symbol">_</a> <a id="40477" href="plfa.part2.Lambda.html#40477" class="Bound">∋x</a><a id="40479" class="Symbol">)</a> <a id="40481" class="Symbol">(</a><a id="40482" href="plfa.part2.Lambda.html#33031" class="InductiveConstructor">S</a> <a id="40484" class="Symbol">_</a> <a id="40486" href="plfa.part2.Lambda.html#40486" class="Bound">∋x′</a><a id="40489" class="Symbol">)</a>  <a id="40492" class="Symbol">=</a>  <a id="40495" href="plfa.part2.Lambda.html#40258" class="Function">∋-injective</a> <a id="40507" href="plfa.part2.Lambda.html#40477" class="Bound">∋x</a> <a id="40510" href="plfa.part2.Lambda.html#40486" class="Bound">∋x′</a>
</pre>{% endraw %}
The typing relation `Γ ⊢ M ⦂ A` is not injective. For example, in any `Γ`
the term `ƛ "x" ⇒ "x"` has type `A ⇒ A` for any type `A`.

### Non-examples

We can also show that terms are _not_ typeable.  For example, here is
a formal proof that it is not possible to type the term
`` `zero · `suc `zero ``.  It cannot be typed, because doing so
requires that the first term in the application is both a natural and
a function:

{% raw %}<pre class="Agda"><a id="nope₁"></a><a id="40947" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#40947" class="Function">nope₁</a> <a id="40953" class="Symbol">:</a> <a id="40955" class="Symbol">∀</a> <a id="40957" class="Symbol">{</a><a id="40958" href="plfa.part2.Lambda.html#40958" class="Bound">A</a><a id="40959" class="Symbol">}</a> <a id="40961" class="Symbol">→</a> <a id="40963" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#535" class="Function Operator">¬</a> <a id="40965" class="Symbol">(</a><a id="40966" href="plfa.part2.Lambda.html#31710" class="InductiveConstructor">∅</a> <a id="40968" href="plfa.part2.Lambda.html#34086" class="Datatype Operator">⊢</a> <a id="40970" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a> <a id="40976" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="40978" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="40983" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a> <a id="40989" href="plfa.part2.Lambda.html#34086" class="Datatype Operator">⦂</a> <a id="40991" href="plfa.part2.Lambda.html#40958" class="Bound">A</a><a id="40992" class="Symbol">)</a>
<a id="40994" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#40947" class="Function">nope₁</a> <a id="41000" class="Symbol">(()</a> <a id="41004" href="plfa.part2.Lambda.html#34330" class="InductiveConstructor Operator">·</a> <a id="41006" class="Symbol">_)</a>
</pre>{% endraw %}
As a second example, here is a formal proof that it is not possible to
type `` ƛ "x" ⇒ ` "x" · ` "x" ``. It cannot be typed, because
doing so requires types `A` and `B` such that `A ⇒ B ≡ A`:

{% raw %}<pre class="Agda"><a id="nope₂"></a><a id="41211" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#41211" class="Function">nope₂</a> <a id="41217" class="Symbol">:</a> <a id="41219" class="Symbol">∀</a> <a id="41221" class="Symbol">{</a><a id="41222" href="plfa.part2.Lambda.html#41222" class="Bound">A</a><a id="41223" class="Symbol">}</a> <a id="41225" class="Symbol">→</a> <a id="41227" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#535" class="Function Operator">¬</a> <a id="41229" class="Symbol">(</a><a id="41230" href="plfa.part2.Lambda.html#31710" class="InductiveConstructor">∅</a> <a id="41232" href="plfa.part2.Lambda.html#34086" class="Datatype Operator">⊢</a> <a id="41234" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">ƛ</a> <a id="41236" class="String">&quot;x&quot;</a> <a id="41240" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a> <a id="41242" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="41244" class="String">&quot;x&quot;</a> <a id="41248" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="41250" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="41252" class="String">&quot;x&quot;</a> <a id="41256" href="plfa.part2.Lambda.html#34086" class="Datatype Operator">⦂</a> <a id="41258" href="plfa.part2.Lambda.html#41222" class="Bound">A</a><a id="41259" class="Symbol">)</a>
<a id="41261" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#41211" class="Function">nope₂</a> <a id="41267" class="Symbol">(</a><a id="41268" href="plfa.part2.Lambda.html#34223" class="InductiveConstructor">⊢ƛ</a> <a id="41271" class="Symbol">(</a><a id="41272" href="plfa.part2.Lambda.html#34143" class="InductiveConstructor">⊢`</a> <a id="41275" href="plfa.part2.Lambda.html#41275" class="Bound">∋x</a> <a id="41278" href="plfa.part2.Lambda.html#34330" class="InductiveConstructor Operator">·</a> <a id="41280" href="plfa.part2.Lambda.html#34143" class="InductiveConstructor">⊢`</a> <a id="41283" href="plfa.part2.Lambda.html#41283" class="Bound">∋x′</a><a id="41286" class="Symbol">))</a>  <a id="41290" class="Symbol">=</a>  <a id="41293" href="plfa.part2.Lambda.html#41338" class="Function">contradiction</a> <a id="41307" class="Symbol">(</a><a id="41308" href="plfa.part2.Lambda.html#40258" class="Function">∋-injective</a> <a id="41320" href="plfa.part2.Lambda.html#41275" class="Bound">∋x</a> <a id="41323" href="plfa.part2.Lambda.html#41283" class="Bound">∋x′</a><a id="41326" class="Symbol">)</a>
  <a id="41330" class="Keyword">where</a>
  <a id="41338" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#41338" class="Function">contradiction</a> <a id="41352" class="Symbol">:</a> <a id="41354" class="Symbol">∀</a> <a id="41356" class="Symbol">{</a><a id="41357" href="plfa.part2.Lambda.html#41357" class="Bound">A</a> <a id="41359" href="plfa.part2.Lambda.html#41359" class="Bound">B</a><a id="41360" class="Symbol">}</a> <a id="41362" class="Symbol">→</a> <a id="41364" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#535" class="Function Operator">¬</a> <a id="41366" class="Symbol">(</a><a id="41367" href="plfa.part2.Lambda.html#41357" class="Bound">A</a> <a id="41369" href="plfa.part2.Lambda.html#30049" class="InductiveConstructor Operator">⇒</a> <a id="41371" href="plfa.part2.Lambda.html#41359" class="Bound">B</a> <a id="41373" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="41375" href="plfa.part2.Lambda.html#41357" class="Bound">A</a><a id="41376" class="Symbol">)</a>
  <a id="41380" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#41338" class="Function">contradiction</a> <a id="41394" class="Symbol">()</a>
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

{% raw %}<pre class="Agda"><a id="42073" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}

#### Exercise `mulᶜ-type` (practice)

Using the term `mulᶜ` you defined earlier, write out the derivation
showing that it is well typed.

{% raw %}<pre class="Agda"><a id="42244" class="Comment">-- Your code goes here</a>
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
