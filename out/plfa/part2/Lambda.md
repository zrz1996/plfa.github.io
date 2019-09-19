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
<a id="3747" class="Keyword">infixl</a> <a id="3754" class="Number">7</a>  <a id="3757" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#34322" class="InductiveConstructor Operator">_·_</a>
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

  ⊥-elim (plfa.part2.Lambda.impossible (`suc (`suc `zero)) (`suc (`suc `zero)))

While postulating the impossible is a useful technique, it must be
used with care, since such postulation could allow us to provide
evidence of _any_ proposition whatsoever, regardless of its truth.

The definition of `plus` can now be written as follows:
{% raw %}<pre class="Agda"><a id="plus′"></a><a id="8462" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#8462" class="Function">plus′</a> <a id="8468" class="Symbol">:</a> <a id="8470" href="plfa.part2.Lambda.html#3796" class="Datatype">Term</a>
<a id="8475" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#8462" class="Function">plus′</a> <a id="8481" class="Symbol">=</a> <a id="8483" href="plfa.part2.Lambda.html#7718" class="Function Operator">μ′</a> <a id="8486" href="plfa.part2.Lambda.html#8593" class="Function">+</a> <a id="8488" href="plfa.part2.Lambda.html#7718" class="Function Operator">⇒</a> <a id="8490" href="plfa.part2.Lambda.html#7383" class="Function Operator">ƛ′</a> <a id="8493" href="plfa.part2.Lambda.html#8607" class="Function">m</a> <a id="8495" href="plfa.part2.Lambda.html#7383" class="Function Operator">⇒</a> <a id="8497" href="plfa.part2.Lambda.html#7383" class="Function Operator">ƛ′</a> <a id="8500" href="plfa.part2.Lambda.html#8621" class="Function">n</a> <a id="8502" href="plfa.part2.Lambda.html#7383" class="Function Operator">⇒</a>
          <a id="8514" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#7504" class="Function Operator">case′</a> <a id="8520" href="plfa.part2.Lambda.html#8607" class="Function">m</a>
            <a id="8534" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#7504" class="Function Operator">[zero⇒</a> <a id="8541" href="plfa.part2.Lambda.html#8621" class="Function">n</a>
            <a id="8555" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#7504" class="Function Operator">|suc</a> <a id="8560" href="plfa.part2.Lambda.html#8607" class="Function">m</a> <a id="8562" href="plfa.part2.Lambda.html#7504" class="Function Operator">⇒</a> <a id="8564" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="8569" class="Symbol">(</a><a id="8570" href="plfa.part2.Lambda.html#8593" class="Function">+</a> <a id="8572" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="8574" href="plfa.part2.Lambda.html#8607" class="Function">m</a> <a id="8576" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="8578" href="plfa.part2.Lambda.html#8621" class="Function">n</a><a id="8579" class="Symbol">)</a> <a id="8581" href="plfa.part2.Lambda.html#7504" class="Function Operator">]</a>
  <a id="8585" class="Keyword">where</a>
  <a id="8593" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#8593" class="Function">+</a>  <a id="8596" class="Symbol">=</a>  <a id="8599" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="8601" class="String">&quot;+&quot;</a>
  <a id="8607" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#8607" class="Function">m</a>  <a id="8610" class="Symbol">=</a>  <a id="8613" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="8615" class="String">&quot;m&quot;</a>
  <a id="8621" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#8621" class="Function">n</a>  <a id="8624" class="Symbol">=</a>  <a id="8627" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="8629" class="String">&quot;n&quot;</a>
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

{% raw %}<pre class="Agda"><a id="12160" class="Keyword">data</a> <a id="Value"></a><a id="12165" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#12165" class="Datatype">Value</a> <a id="12171" class="Symbol">:</a> <a id="12173" href="plfa.part2.Lambda.html#3796" class="Datatype">Term</a> <a id="12178" class="Symbol">→</a> <a id="12180" class="PrimitiveType">Set</a> <a id="12184" class="Keyword">where</a>

  <a id="Value.V-ƛ"></a><a id="12193" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#12193" class="InductiveConstructor">V-ƛ</a> <a id="12197" class="Symbol">:</a> <a id="12199" class="Symbol">∀</a> <a id="12201" class="Symbol">{</a><a id="12202" href="plfa.part2.Lambda.html#12202" class="Bound">x</a> <a id="12204" href="plfa.part2.Lambda.html#12204" class="Bound">N</a><a id="12205" class="Symbol">}</a>
      <a id="12213" class="Comment">---------------</a>
    <a id="12233" class="Symbol">→</a> <a id="12235" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#12165" class="Datatype">Value</a> <a id="12241" class="Symbol">(</a><a id="12242" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">ƛ</a> <a id="12244" href="plfa.part2.Lambda.html#12202" class="Bound">x</a> <a id="12246" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a> <a id="12248" href="plfa.part2.Lambda.html#12204" class="Bound">N</a><a id="12249" class="Symbol">)</a>

  <a id="Value.V-zero"></a><a id="12254" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#12254" class="InductiveConstructor">V-zero</a> <a id="12261" class="Symbol">:</a>
      <a id="12269" class="Comment">-----------</a>
      <a id="12287" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#12165" class="Datatype">Value</a> <a id="12293" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a>

  <a id="Value.V-suc"></a><a id="12302" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#12302" class="InductiveConstructor">V-suc</a> <a id="12308" class="Symbol">:</a> <a id="12310" class="Symbol">∀</a> <a id="12312" class="Symbol">{</a><a id="12313" href="plfa.part2.Lambda.html#12313" class="Bound">V</a><a id="12314" class="Symbol">}</a>
    <a id="12320" class="Symbol">→</a> <a id="12322" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#12165" class="Datatype">Value</a> <a id="12328" href="plfa.part2.Lambda.html#12313" class="Bound">V</a>
      <a id="12336" class="Comment">--------------</a>
    <a id="12355" class="Symbol">→</a> <a id="12357" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#12165" class="Datatype">Value</a> <a id="12363" class="Symbol">(</a><a id="12364" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="12369" href="plfa.part2.Lambda.html#12313" class="Bound">V</a><a id="12370" class="Symbol">)</a>
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

{% raw %}<pre class="Agda"><a id="15531" class="Keyword">infix</a> <a id="15537" class="Number">9</a> <a id="15539" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#15548" class="Function Operator">_[_:=_]</a>

<a id="_[_:=_]"></a><a id="15548" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#15548" class="Function Operator">_[_:=_]</a> <a id="15556" class="Symbol">:</a> <a id="15558" href="plfa.part2.Lambda.html#3796" class="Datatype">Term</a> <a id="15563" class="Symbol">→</a> <a id="15565" href="plfa.part2.Lambda.html#3695" class="Function">Id</a> <a id="15568" class="Symbol">→</a> <a id="15570" href="plfa.part2.Lambda.html#3796" class="Datatype">Term</a> <a id="15575" class="Symbol">→</a> <a id="15577" href="plfa.part2.Lambda.html#3796" class="Datatype">Term</a>
<a id="15582" class="Symbol">(</a><a id="15583" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3815" class="InductiveConstructor Operator">`</a> <a id="15585" href="plfa.part2.Lambda.html#15585" class="Bound">x</a><a id="15586" class="Symbol">)</a> <a id="15588" href="plfa.part2.Lambda.html#15548" class="Function Operator">[</a> <a id="15590" href="plfa.part2.Lambda.html#15590" class="Bound">y</a> <a id="15592" href="plfa.part2.Lambda.html#15548" class="Function Operator">:=</a> <a id="15595" href="plfa.part2.Lambda.html#15595" class="Bound">V</a> <a id="15597" href="plfa.part2.Lambda.html#15548" class="Function Operator">]</a> <a id="15599" class="Keyword">with</a> <a id="15604" href="plfa.part2.Lambda.html#15585" class="Bound">x</a> <a id="15606" href="https://agda.github.io/agda-stdlib/v1.1/Data.String.Properties.html#2569" class="Function Operator">≟</a> <a id="15608" href="plfa.part2.Lambda.html#15590" class="Bound">y</a>
<a id="15610" class="Symbol">...</a> <a id="15614" class="Symbol">|</a> <a id="15616" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#641" class="InductiveConstructor">yes</a> <a id="15620" class="Symbol">_</a>          <a id="15631" class="Symbol">=</a>  <a id="15634" class="Bound">V</a>
<a id="15636" class="Symbol">...</a> <a id="15640" class="Symbol">|</a> <a id="15642" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#668" class="InductiveConstructor">no</a>  <a id="15646" class="Symbol">_</a>          <a id="15657" class="Symbol">=</a>  <a id="15660" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3815" class="InductiveConstructor Operator">`</a> <a id="15662" class="Bound">x</a>
<a id="15664" class="Symbol">(</a><a id="15665" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3854" class="InductiveConstructor Operator">ƛ</a> <a id="15667" href="plfa.part2.Lambda.html#15667" class="Bound">x</a> <a id="15669" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a> <a id="15671" href="plfa.part2.Lambda.html#15671" class="Bound">N</a><a id="15672" class="Symbol">)</a> <a id="15674" href="plfa.part2.Lambda.html#15548" class="Function Operator">[</a> <a id="15676" href="plfa.part2.Lambda.html#15676" class="Bound">y</a> <a id="15678" href="plfa.part2.Lambda.html#15548" class="Function Operator">:=</a> <a id="15681" href="plfa.part2.Lambda.html#15681" class="Bound">V</a> <a id="15683" href="plfa.part2.Lambda.html#15548" class="Function Operator">]</a> <a id="15685" class="Keyword">with</a> <a id="15690" href="plfa.part2.Lambda.html#15667" class="Bound">x</a> <a id="15692" href="https://agda.github.io/agda-stdlib/v1.1/Data.String.Properties.html#2569" class="Function Operator">≟</a> <a id="15694" href="plfa.part2.Lambda.html#15676" class="Bound">y</a>
<a id="15696" class="Symbol">...</a> <a id="15700" class="Symbol">|</a> <a id="15702" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#641" class="InductiveConstructor">yes</a> <a id="15706" class="Symbol">_</a>          <a id="15717" class="Symbol">=</a>  <a id="15720" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3854" class="InductiveConstructor Operator">ƛ</a> <a id="15722" class="Bound">x</a> <a id="15724" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a> <a id="15726" class="Bound">N</a>
<a id="15728" class="Symbol">...</a> <a id="15732" class="Symbol">|</a> <a id="15734" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#668" class="InductiveConstructor">no</a>  <a id="15738" class="Symbol">_</a>          <a id="15749" class="Symbol">=</a>  <a id="15752" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3854" class="InductiveConstructor Operator">ƛ</a> <a id="15754" class="Bound">x</a> <a id="15756" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a> <a id="15758" class="Bound">N</a> <a id="15760" href="plfa.part2.Lambda.html#15548" class="Function Operator">[</a> <a id="15762" class="Bound">y</a> <a id="15764" href="plfa.part2.Lambda.html#15548" class="Function Operator">:=</a> <a id="15767" class="Bound">V</a> <a id="15769" href="plfa.part2.Lambda.html#15548" class="Function Operator">]</a>
<a id="15771" class="Symbol">(</a><a id="15772" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#15772" class="Bound">L</a> <a id="15774" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="15776" href="plfa.part2.Lambda.html#15776" class="Bound">M</a><a id="15777" class="Symbol">)</a> <a id="15779" href="plfa.part2.Lambda.html#15548" class="Function Operator">[</a> <a id="15781" href="plfa.part2.Lambda.html#15781" class="Bound">y</a> <a id="15783" href="plfa.part2.Lambda.html#15548" class="Function Operator">:=</a> <a id="15786" href="plfa.part2.Lambda.html#15786" class="Bound">V</a> <a id="15788" href="plfa.part2.Lambda.html#15548" class="Function Operator">]</a>   <a id="15792" class="Symbol">=</a>  <a id="15795" href="plfa.part2.Lambda.html#15772" class="Bound">L</a> <a id="15797" href="plfa.part2.Lambda.html#15548" class="Function Operator">[</a> <a id="15799" href="plfa.part2.Lambda.html#15781" class="Bound">y</a> <a id="15801" href="plfa.part2.Lambda.html#15548" class="Function Operator">:=</a> <a id="15804" href="plfa.part2.Lambda.html#15786" class="Bound">V</a> <a id="15806" href="plfa.part2.Lambda.html#15548" class="Function Operator">]</a> <a id="15808" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="15810" href="plfa.part2.Lambda.html#15776" class="Bound">M</a> <a id="15812" href="plfa.part2.Lambda.html#15548" class="Function Operator">[</a> <a id="15814" href="plfa.part2.Lambda.html#15781" class="Bound">y</a> <a id="15816" href="plfa.part2.Lambda.html#15548" class="Function Operator">:=</a> <a id="15819" href="plfa.part2.Lambda.html#15786" class="Bound">V</a> <a id="15821" href="plfa.part2.Lambda.html#15548" class="Function Operator">]</a>
<a id="15823" class="Symbol">(</a><a id="15824" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3948" class="InductiveConstructor">`zero</a><a id="15829" class="Symbol">)</a> <a id="15831" href="plfa.part2.Lambda.html#15548" class="Function Operator">[</a> <a id="15833" href="plfa.part2.Lambda.html#15833" class="Bound">y</a> <a id="15835" href="plfa.part2.Lambda.html#15548" class="Function Operator">:=</a> <a id="15838" href="plfa.part2.Lambda.html#15838" class="Bound">V</a> <a id="15840" href="plfa.part2.Lambda.html#15548" class="Function Operator">]</a>   <a id="15844" class="Symbol">=</a>  <a id="15847" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a>
<a id="15853" class="Symbol">(</a><a id="15854" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3982" class="InductiveConstructor Operator">`suc</a> <a id="15859" href="plfa.part2.Lambda.html#15859" class="Bound">M</a><a id="15860" class="Symbol">)</a> <a id="15862" href="plfa.part2.Lambda.html#15548" class="Function Operator">[</a> <a id="15864" href="plfa.part2.Lambda.html#15864" class="Bound">y</a> <a id="15866" href="plfa.part2.Lambda.html#15548" class="Function Operator">:=</a> <a id="15869" href="plfa.part2.Lambda.html#15869" class="Bound">V</a> <a id="15871" href="plfa.part2.Lambda.html#15548" class="Function Operator">]</a>  <a id="15874" class="Symbol">=</a>  <a id="15877" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="15882" href="plfa.part2.Lambda.html#15859" class="Bound">M</a> <a id="15884" href="plfa.part2.Lambda.html#15548" class="Function Operator">[</a> <a id="15886" href="plfa.part2.Lambda.html#15864" class="Bound">y</a> <a id="15888" href="plfa.part2.Lambda.html#15548" class="Function Operator">:=</a> <a id="15891" href="plfa.part2.Lambda.html#15869" class="Bound">V</a> <a id="15893" href="plfa.part2.Lambda.html#15548" class="Function Operator">]</a>
<a id="15895" class="Symbol">(</a><a id="15896" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#4023" class="InductiveConstructor Operator">case</a> <a id="15901" href="plfa.part2.Lambda.html#15901" class="Bound">L</a> <a id="15903" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">[zero⇒</a> <a id="15910" href="plfa.part2.Lambda.html#15910" class="Bound">M</a> <a id="15912" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">|suc</a> <a id="15917" href="plfa.part2.Lambda.html#15917" class="Bound">x</a> <a id="15919" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">⇒</a> <a id="15921" href="plfa.part2.Lambda.html#15921" class="Bound">N</a> <a id="15923" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">]</a><a id="15924" class="Symbol">)</a> <a id="15926" href="plfa.part2.Lambda.html#15548" class="Function Operator">[</a> <a id="15928" href="plfa.part2.Lambda.html#15928" class="Bound">y</a> <a id="15930" href="plfa.part2.Lambda.html#15548" class="Function Operator">:=</a> <a id="15933" href="plfa.part2.Lambda.html#15933" class="Bound">V</a> <a id="15935" href="plfa.part2.Lambda.html#15548" class="Function Operator">]</a> <a id="15937" class="Keyword">with</a> <a id="15942" href="plfa.part2.Lambda.html#15917" class="Bound">x</a> <a id="15944" href="https://agda.github.io/agda-stdlib/v1.1/Data.String.Properties.html#2569" class="Function Operator">≟</a> <a id="15946" href="plfa.part2.Lambda.html#15928" class="Bound">y</a>
<a id="15948" class="Symbol">...</a> <a id="15952" class="Symbol">|</a> <a id="15954" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#641" class="InductiveConstructor">yes</a> <a id="15958" class="Symbol">_</a>          <a id="15969" class="Symbol">=</a>  <a id="15972" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#4023" class="InductiveConstructor Operator">case</a> <a id="15977" class="Bound">L</a> <a id="15979" href="plfa.part2.Lambda.html#15548" class="Function Operator">[</a> <a id="15981" class="Bound">y</a> <a id="15983" href="plfa.part2.Lambda.html#15548" class="Function Operator">:=</a> <a id="15986" class="Bound">V</a> <a id="15988" href="plfa.part2.Lambda.html#15548" class="Function Operator">]</a> <a id="15990" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">[zero⇒</a> <a id="15997" class="Bound">M</a> <a id="15999" href="plfa.part2.Lambda.html#15548" class="Function Operator">[</a> <a id="16001" class="Bound">y</a> <a id="16003" href="plfa.part2.Lambda.html#15548" class="Function Operator">:=</a> <a id="16006" class="Bound">V</a> <a id="16008" href="plfa.part2.Lambda.html#15548" class="Function Operator">]</a> <a id="16010" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">|suc</a> <a id="16015" class="Bound">x</a> <a id="16017" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">⇒</a> <a id="16019" class="Bound">N</a> <a id="16021" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">]</a>
<a id="16023" class="Symbol">...</a> <a id="16027" class="Symbol">|</a> <a id="16029" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#668" class="InductiveConstructor">no</a>  <a id="16033" class="Symbol">_</a>          <a id="16044" class="Symbol">=</a>  <a id="16047" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#4023" class="InductiveConstructor Operator">case</a> <a id="16052" class="Bound">L</a> <a id="16054" href="plfa.part2.Lambda.html#15548" class="Function Operator">[</a> <a id="16056" class="Bound">y</a> <a id="16058" href="plfa.part2.Lambda.html#15548" class="Function Operator">:=</a> <a id="16061" class="Bound">V</a> <a id="16063" href="plfa.part2.Lambda.html#15548" class="Function Operator">]</a> <a id="16065" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">[zero⇒</a> <a id="16072" class="Bound">M</a> <a id="16074" href="plfa.part2.Lambda.html#15548" class="Function Operator">[</a> <a id="16076" class="Bound">y</a> <a id="16078" href="plfa.part2.Lambda.html#15548" class="Function Operator">:=</a> <a id="16081" class="Bound">V</a> <a id="16083" href="plfa.part2.Lambda.html#15548" class="Function Operator">]</a> <a id="16085" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">|suc</a> <a id="16090" class="Bound">x</a> <a id="16092" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">⇒</a> <a id="16094" class="Bound">N</a> <a id="16096" href="plfa.part2.Lambda.html#15548" class="Function Operator">[</a> <a id="16098" class="Bound">y</a> <a id="16100" href="plfa.part2.Lambda.html#15548" class="Function Operator">:=</a> <a id="16103" class="Bound">V</a> <a id="16105" href="plfa.part2.Lambda.html#15548" class="Function Operator">]</a> <a id="16107" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">]</a>
<a id="16109" class="Symbol">(</a><a id="16110" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#4083" class="InductiveConstructor Operator">μ</a> <a id="16112" href="plfa.part2.Lambda.html#16112" class="Bound">x</a> <a id="16114" href="plfa.part2.Lambda.html#4083" class="InductiveConstructor Operator">⇒</a> <a id="16116" href="plfa.part2.Lambda.html#16116" class="Bound">N</a><a id="16117" class="Symbol">)</a> <a id="16119" href="plfa.part2.Lambda.html#15548" class="Function Operator">[</a> <a id="16121" href="plfa.part2.Lambda.html#16121" class="Bound">y</a> <a id="16123" href="plfa.part2.Lambda.html#15548" class="Function Operator">:=</a> <a id="16126" href="plfa.part2.Lambda.html#16126" class="Bound">V</a> <a id="16128" href="plfa.part2.Lambda.html#15548" class="Function Operator">]</a> <a id="16130" class="Keyword">with</a> <a id="16135" href="plfa.part2.Lambda.html#16112" class="Bound">x</a> <a id="16137" href="https://agda.github.io/agda-stdlib/v1.1/Data.String.Properties.html#2569" class="Function Operator">≟</a> <a id="16139" href="plfa.part2.Lambda.html#16121" class="Bound">y</a>
<a id="16141" class="Symbol">...</a> <a id="16145" class="Symbol">|</a> <a id="16147" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#641" class="InductiveConstructor">yes</a> <a id="16151" class="Symbol">_</a>          <a id="16162" class="Symbol">=</a>  <a id="16165" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#4083" class="InductiveConstructor Operator">μ</a> <a id="16167" class="Bound">x</a> <a id="16169" href="plfa.part2.Lambda.html#4083" class="InductiveConstructor Operator">⇒</a> <a id="16171" class="Bound">N</a>
<a id="16173" class="Symbol">...</a> <a id="16177" class="Symbol">|</a> <a id="16179" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#668" class="InductiveConstructor">no</a>  <a id="16183" class="Symbol">_</a>          <a id="16194" class="Symbol">=</a>  <a id="16197" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#4083" class="InductiveConstructor Operator">μ</a> <a id="16199" class="Bound">x</a> <a id="16201" href="plfa.part2.Lambda.html#4083" class="InductiveConstructor Operator">⇒</a> <a id="16203" class="Bound">N</a> <a id="16205" href="plfa.part2.Lambda.html#15548" class="Function Operator">[</a> <a id="16207" class="Bound">y</a> <a id="16209" href="plfa.part2.Lambda.html#15548" class="Function Operator">:=</a> <a id="16212" class="Bound">V</a> <a id="16214" href="plfa.part2.Lambda.html#15548" class="Function Operator">]</a>
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

{% raw %}<pre class="Agda"><a id="16981" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#16981" class="Function">_</a> <a id="16983" class="Symbol">:</a> <a id="16985" class="Symbol">(</a><a id="16986" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">ƛ</a> <a id="16988" class="String">&quot;z&quot;</a> <a id="16992" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a> <a id="16994" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="16996" class="String">&quot;s&quot;</a> <a id="17000" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="17002" class="Symbol">(</a><a id="17003" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="17005" class="String">&quot;s&quot;</a> <a id="17009" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="17011" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="17013" class="String">&quot;z&quot;</a><a id="17016" class="Symbol">))</a> <a id="17019" href="plfa.part2.Lambda.html#15548" class="Function Operator">[</a> <a id="17021" class="String">&quot;s&quot;</a> <a id="17025" href="plfa.part2.Lambda.html#15548" class="Function Operator">:=</a> <a id="17028" href="plfa.part2.Lambda.html#5938" class="Function">sucᶜ</a> <a id="17033" href="plfa.part2.Lambda.html#15548" class="Function Operator">]</a> <a id="17035" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="17037" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">ƛ</a> <a id="17039" class="String">&quot;z&quot;</a> <a id="17043" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a> <a id="17045" href="plfa.part2.Lambda.html#5938" class="Function">sucᶜ</a> <a id="17050" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="17052" class="Symbol">(</a><a id="17053" href="plfa.part2.Lambda.html#5938" class="Function">sucᶜ</a> <a id="17058" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="17060" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="17062" class="String">&quot;z&quot;</a><a id="17065" class="Symbol">)</a>
<a id="17067" class="Symbol">_</a> <a id="17069" class="Symbol">=</a> <a id="17071" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>

<a id="17077" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#17077" class="Function">_</a> <a id="17079" class="Symbol">:</a> <a id="17081" class="Symbol">(</a><a id="17082" href="plfa.part2.Lambda.html#5938" class="Function">sucᶜ</a> <a id="17087" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="17089" class="Symbol">(</a><a id="17090" href="plfa.part2.Lambda.html#5938" class="Function">sucᶜ</a> <a id="17095" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="17097" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="17099" class="String">&quot;z&quot;</a><a id="17102" class="Symbol">))</a> <a id="17105" href="plfa.part2.Lambda.html#15548" class="Function Operator">[</a> <a id="17107" class="String">&quot;z&quot;</a> <a id="17111" href="plfa.part2.Lambda.html#15548" class="Function Operator">:=</a> <a id="17114" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a> <a id="17120" href="plfa.part2.Lambda.html#15548" class="Function Operator">]</a> <a id="17122" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="17124" href="plfa.part2.Lambda.html#5938" class="Function">sucᶜ</a> <a id="17129" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="17131" class="Symbol">(</a><a id="17132" href="plfa.part2.Lambda.html#5938" class="Function">sucᶜ</a> <a id="17137" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="17139" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a><a id="17144" class="Symbol">)</a>
<a id="17146" class="Symbol">_</a> <a id="17148" class="Symbol">=</a> <a id="17150" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>

<a id="17156" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#17156" class="Function">_</a> <a id="17158" class="Symbol">:</a> <a id="17160" class="Symbol">(</a><a id="17161" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">ƛ</a> <a id="17163" class="String">&quot;x&quot;</a> <a id="17167" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a> <a id="17169" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="17171" class="String">&quot;y&quot;</a><a id="17174" class="Symbol">)</a> <a id="17176" href="plfa.part2.Lambda.html#15548" class="Function Operator">[</a> <a id="17178" class="String">&quot;y&quot;</a> <a id="17182" href="plfa.part2.Lambda.html#15548" class="Function Operator">:=</a> <a id="17185" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a> <a id="17191" href="plfa.part2.Lambda.html#15548" class="Function Operator">]</a> <a id="17193" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="17195" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">ƛ</a> <a id="17197" class="String">&quot;x&quot;</a> <a id="17201" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a> <a id="17203" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a>
<a id="17209" class="Symbol">_</a> <a id="17211" class="Symbol">=</a> <a id="17213" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>

<a id="17219" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#17219" class="Function">_</a> <a id="17221" class="Symbol">:</a> <a id="17223" class="Symbol">(</a><a id="17224" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">ƛ</a> <a id="17226" class="String">&quot;x&quot;</a> <a id="17230" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a> <a id="17232" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="17234" class="String">&quot;x&quot;</a><a id="17237" class="Symbol">)</a> <a id="17239" href="plfa.part2.Lambda.html#15548" class="Function Operator">[</a> <a id="17241" class="String">&quot;x&quot;</a> <a id="17245" href="plfa.part2.Lambda.html#15548" class="Function Operator">:=</a> <a id="17248" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a> <a id="17254" href="plfa.part2.Lambda.html#15548" class="Function Operator">]</a> <a id="17256" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="17258" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">ƛ</a> <a id="17260" class="String">&quot;x&quot;</a> <a id="17264" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a> <a id="17266" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="17268" class="String">&quot;x&quot;</a>
<a id="17272" class="Symbol">_</a> <a id="17274" class="Symbol">=</a> <a id="17276" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>

<a id="17282" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#17282" class="Function">_</a> <a id="17284" class="Symbol">:</a> <a id="17286" class="Symbol">(</a><a id="17287" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">ƛ</a> <a id="17289" class="String">&quot;y&quot;</a> <a id="17293" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a> <a id="17295" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="17297" class="String">&quot;y&quot;</a><a id="17300" class="Symbol">)</a> <a id="17302" href="plfa.part2.Lambda.html#15548" class="Function Operator">[</a> <a id="17304" class="String">&quot;x&quot;</a> <a id="17308" href="plfa.part2.Lambda.html#15548" class="Function Operator">:=</a> <a id="17311" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a> <a id="17317" href="plfa.part2.Lambda.html#15548" class="Function Operator">]</a> <a id="17319" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="17321" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">ƛ</a> <a id="17323" class="String">&quot;y&quot;</a> <a id="17327" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a> <a id="17329" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="17331" class="String">&quot;y&quot;</a>
<a id="17335" class="Symbol">_</a> <a id="17337" class="Symbol">=</a> <a id="17339" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>
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

{% raw %}<pre class="Agda"><a id="17962" class="Comment">-- Your code goes here</a>
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

{% raw %}<pre class="Agda"><a id="20170" class="Keyword">infix</a> <a id="20176" class="Number">4</a> <a id="20178" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#20189" class="Datatype Operator">_—→_</a>

<a id="20184" class="Keyword">data</a> <a id="_—→_"></a><a id="20189" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#20189" class="Datatype Operator">_—→_</a> <a id="20194" class="Symbol">:</a> <a id="20196" href="plfa.part2.Lambda.html#3796" class="Datatype">Term</a> <a id="20201" class="Symbol">→</a> <a id="20203" href="plfa.part2.Lambda.html#3796" class="Datatype">Term</a> <a id="20208" class="Symbol">→</a> <a id="20210" class="PrimitiveType">Set</a> <a id="20214" class="Keyword">where</a>

  <a id="_—→_.ξ-·₁"></a><a id="20223" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#20223" class="InductiveConstructor">ξ-·₁</a> <a id="20228" class="Symbol">:</a> <a id="20230" class="Symbol">∀</a> <a id="20232" class="Symbol">{</a><a id="20233" href="plfa.part2.Lambda.html#20233" class="Bound">L</a> <a id="20235" href="plfa.part2.Lambda.html#20235" class="Bound">L′</a> <a id="20238" href="plfa.part2.Lambda.html#20238" class="Bound">M</a><a id="20239" class="Symbol">}</a>
    <a id="20245" class="Symbol">→</a> <a id="20247" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#20233" class="Bound">L</a> <a id="20249" href="plfa.part2.Lambda.html#20189" class="Datatype Operator">—→</a> <a id="20252" href="plfa.part2.Lambda.html#20235" class="Bound">L′</a>
      <a id="20261" class="Comment">-----------------</a>
    <a id="20283" class="Symbol">→</a> <a id="20285" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#20233" class="Bound">L</a> <a id="20287" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="20289" href="plfa.part2.Lambda.html#20238" class="Bound">M</a> <a id="20291" href="plfa.part2.Lambda.html#20189" class="Datatype Operator">—→</a> <a id="20294" href="plfa.part2.Lambda.html#20235" class="Bound">L′</a> <a id="20297" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="20299" href="plfa.part2.Lambda.html#20238" class="Bound">M</a>

  <a id="_—→_.ξ-·₂"></a><a id="20304" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#20304" class="InductiveConstructor">ξ-·₂</a> <a id="20309" class="Symbol">:</a> <a id="20311" class="Symbol">∀</a> <a id="20313" class="Symbol">{</a><a id="20314" href="plfa.part2.Lambda.html#20314" class="Bound">V</a> <a id="20316" href="plfa.part2.Lambda.html#20316" class="Bound">M</a> <a id="20318" href="plfa.part2.Lambda.html#20318" class="Bound">M′</a><a id="20320" class="Symbol">}</a>
    <a id="20326" class="Symbol">→</a> <a id="20328" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#12165" class="Datatype">Value</a> <a id="20334" href="plfa.part2.Lambda.html#20314" class="Bound">V</a>
    <a id="20340" class="Symbol">→</a> <a id="20342" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#20316" class="Bound">M</a> <a id="20344" href="plfa.part2.Lambda.html#20189" class="Datatype Operator">—→</a> <a id="20347" href="plfa.part2.Lambda.html#20318" class="Bound">M′</a>
      <a id="20356" class="Comment">-----------------</a>
    <a id="20378" class="Symbol">→</a> <a id="20380" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#20314" class="Bound">V</a> <a id="20382" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="20384" href="plfa.part2.Lambda.html#20316" class="Bound">M</a> <a id="20386" href="plfa.part2.Lambda.html#20189" class="Datatype Operator">—→</a> <a id="20389" href="plfa.part2.Lambda.html#20314" class="Bound">V</a> <a id="20391" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="20393" href="plfa.part2.Lambda.html#20318" class="Bound">M′</a>

  <a id="_—→_.β-ƛ"></a><a id="20399" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#20399" class="InductiveConstructor">β-ƛ</a> <a id="20403" class="Symbol">:</a> <a id="20405" class="Symbol">∀</a> <a id="20407" class="Symbol">{</a><a id="20408" href="plfa.part2.Lambda.html#20408" class="Bound">x</a> <a id="20410" href="plfa.part2.Lambda.html#20410" class="Bound">N</a> <a id="20412" href="plfa.part2.Lambda.html#20412" class="Bound">V</a><a id="20413" class="Symbol">}</a>
    <a id="20419" class="Symbol">→</a> <a id="20421" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#12165" class="Datatype">Value</a> <a id="20427" href="plfa.part2.Lambda.html#20412" class="Bound">V</a>
      <a id="20435" class="Comment">------------------------------</a>
    <a id="20470" class="Symbol">→</a> <a id="20472" class="Symbol">(</a><a id="20473" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3854" class="InductiveConstructor Operator">ƛ</a> <a id="20475" href="plfa.part2.Lambda.html#20408" class="Bound">x</a> <a id="20477" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a> <a id="20479" href="plfa.part2.Lambda.html#20410" class="Bound">N</a><a id="20480" class="Symbol">)</a> <a id="20482" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="20484" href="plfa.part2.Lambda.html#20412" class="Bound">V</a> <a id="20486" href="plfa.part2.Lambda.html#20189" class="Datatype Operator">—→</a> <a id="20489" href="plfa.part2.Lambda.html#20410" class="Bound">N</a> <a id="20491" href="plfa.part2.Lambda.html#15548" class="Function Operator">[</a> <a id="20493" href="plfa.part2.Lambda.html#20408" class="Bound">x</a> <a id="20495" href="plfa.part2.Lambda.html#15548" class="Function Operator">:=</a> <a id="20498" href="plfa.part2.Lambda.html#20412" class="Bound">V</a> <a id="20500" href="plfa.part2.Lambda.html#15548" class="Function Operator">]</a>

  <a id="_—→_.ξ-suc"></a><a id="20505" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#20505" class="InductiveConstructor">ξ-suc</a> <a id="20511" class="Symbol">:</a> <a id="20513" class="Symbol">∀</a> <a id="20515" class="Symbol">{</a><a id="20516" href="plfa.part2.Lambda.html#20516" class="Bound">M</a> <a id="20518" href="plfa.part2.Lambda.html#20518" class="Bound">M′</a><a id="20520" class="Symbol">}</a>
    <a id="20526" class="Symbol">→</a> <a id="20528" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#20516" class="Bound">M</a> <a id="20530" href="plfa.part2.Lambda.html#20189" class="Datatype Operator">—→</a> <a id="20533" href="plfa.part2.Lambda.html#20518" class="Bound">M′</a>
      <a id="20542" class="Comment">------------------</a>
    <a id="20565" class="Symbol">→</a> <a id="20567" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3982" class="InductiveConstructor Operator">`suc</a> <a id="20572" href="plfa.part2.Lambda.html#20516" class="Bound">M</a> <a id="20574" href="plfa.part2.Lambda.html#20189" class="Datatype Operator">—→</a> <a id="20577" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="20582" href="plfa.part2.Lambda.html#20518" class="Bound">M′</a>

  <a id="_—→_.ξ-case"></a><a id="20588" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#20588" class="InductiveConstructor">ξ-case</a> <a id="20595" class="Symbol">:</a> <a id="20597" class="Symbol">∀</a> <a id="20599" class="Symbol">{</a><a id="20600" href="plfa.part2.Lambda.html#20600" class="Bound">x</a> <a id="20602" href="plfa.part2.Lambda.html#20602" class="Bound">L</a> <a id="20604" href="plfa.part2.Lambda.html#20604" class="Bound">L′</a> <a id="20607" href="plfa.part2.Lambda.html#20607" class="Bound">M</a> <a id="20609" href="plfa.part2.Lambda.html#20609" class="Bound">N</a><a id="20610" class="Symbol">}</a>
    <a id="20616" class="Symbol">→</a> <a id="20618" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#20602" class="Bound">L</a> <a id="20620" href="plfa.part2.Lambda.html#20189" class="Datatype Operator">—→</a> <a id="20623" href="plfa.part2.Lambda.html#20604" class="Bound">L′</a>
      <a id="20632" class="Comment">-----------------------------------------------------------------</a>
    <a id="20702" class="Symbol">→</a> <a id="20704" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#4023" class="InductiveConstructor Operator">case</a> <a id="20709" href="plfa.part2.Lambda.html#20602" class="Bound">L</a> <a id="20711" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">[zero⇒</a> <a id="20718" href="plfa.part2.Lambda.html#20607" class="Bound">M</a> <a id="20720" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">|suc</a> <a id="20725" href="plfa.part2.Lambda.html#20600" class="Bound">x</a> <a id="20727" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">⇒</a> <a id="20729" href="plfa.part2.Lambda.html#20609" class="Bound">N</a> <a id="20731" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">]</a> <a id="20733" href="plfa.part2.Lambda.html#20189" class="Datatype Operator">—→</a> <a id="20736" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">case</a> <a id="20741" href="plfa.part2.Lambda.html#20604" class="Bound">L′</a> <a id="20744" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">[zero⇒</a> <a id="20751" href="plfa.part2.Lambda.html#20607" class="Bound">M</a> <a id="20753" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">|suc</a> <a id="20758" href="plfa.part2.Lambda.html#20600" class="Bound">x</a> <a id="20760" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">⇒</a> <a id="20762" href="plfa.part2.Lambda.html#20609" class="Bound">N</a> <a id="20764" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">]</a>

  <a id="_—→_.β-zero"></a><a id="20769" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#20769" class="InductiveConstructor">β-zero</a> <a id="20776" class="Symbol">:</a> <a id="20778" class="Symbol">∀</a> <a id="20780" class="Symbol">{</a><a id="20781" href="plfa.part2.Lambda.html#20781" class="Bound">x</a> <a id="20783" href="plfa.part2.Lambda.html#20783" class="Bound">M</a> <a id="20785" href="plfa.part2.Lambda.html#20785" class="Bound">N</a><a id="20786" class="Symbol">}</a>
      <a id="20794" class="Comment">----------------------------------------</a>
    <a id="20839" class="Symbol">→</a> <a id="20841" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#4023" class="InductiveConstructor Operator">case</a> <a id="20846" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a> <a id="20852" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">[zero⇒</a> <a id="20859" href="plfa.part2.Lambda.html#20783" class="Bound">M</a> <a id="20861" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">|suc</a> <a id="20866" href="plfa.part2.Lambda.html#20781" class="Bound">x</a> <a id="20868" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">⇒</a> <a id="20870" href="plfa.part2.Lambda.html#20785" class="Bound">N</a> <a id="20872" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">]</a> <a id="20874" href="plfa.part2.Lambda.html#20189" class="Datatype Operator">—→</a> <a id="20877" href="plfa.part2.Lambda.html#20783" class="Bound">M</a>

  <a id="_—→_.β-suc"></a><a id="20882" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#20882" class="InductiveConstructor">β-suc</a> <a id="20888" class="Symbol">:</a> <a id="20890" class="Symbol">∀</a> <a id="20892" class="Symbol">{</a><a id="20893" href="plfa.part2.Lambda.html#20893" class="Bound">x</a> <a id="20895" href="plfa.part2.Lambda.html#20895" class="Bound">V</a> <a id="20897" href="plfa.part2.Lambda.html#20897" class="Bound">M</a> <a id="20899" href="plfa.part2.Lambda.html#20899" class="Bound">N</a><a id="20900" class="Symbol">}</a>
    <a id="20906" class="Symbol">→</a> <a id="20908" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#12165" class="Datatype">Value</a> <a id="20914" href="plfa.part2.Lambda.html#20895" class="Bound">V</a>
      <a id="20922" class="Comment">---------------------------------------------------</a>
    <a id="20978" class="Symbol">→</a> <a id="20980" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#4023" class="InductiveConstructor Operator">case</a> <a id="20985" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="20990" href="plfa.part2.Lambda.html#20895" class="Bound">V</a> <a id="20992" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">[zero⇒</a> <a id="20999" href="plfa.part2.Lambda.html#20897" class="Bound">M</a> <a id="21001" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">|suc</a> <a id="21006" href="plfa.part2.Lambda.html#20893" class="Bound">x</a> <a id="21008" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">⇒</a> <a id="21010" href="plfa.part2.Lambda.html#20899" class="Bound">N</a> <a id="21012" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">]</a> <a id="21014" href="plfa.part2.Lambda.html#20189" class="Datatype Operator">—→</a> <a id="21017" href="plfa.part2.Lambda.html#20899" class="Bound">N</a> <a id="21019" href="plfa.part2.Lambda.html#15548" class="Function Operator">[</a> <a id="21021" href="plfa.part2.Lambda.html#20893" class="Bound">x</a> <a id="21023" href="plfa.part2.Lambda.html#15548" class="Function Operator">:=</a> <a id="21026" href="plfa.part2.Lambda.html#20895" class="Bound">V</a> <a id="21028" href="plfa.part2.Lambda.html#15548" class="Function Operator">]</a>

  <a id="_—→_.β-μ"></a><a id="21033" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#21033" class="InductiveConstructor">β-μ</a> <a id="21037" class="Symbol">:</a> <a id="21039" class="Symbol">∀</a> <a id="21041" class="Symbol">{</a><a id="21042" href="plfa.part2.Lambda.html#21042" class="Bound">x</a> <a id="21044" href="plfa.part2.Lambda.html#21044" class="Bound">M</a><a id="21045" class="Symbol">}</a>
      <a id="21053" class="Comment">------------------------------</a>
    <a id="21088" class="Symbol">→</a> <a id="21090" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#4083" class="InductiveConstructor Operator">μ</a> <a id="21092" href="plfa.part2.Lambda.html#21042" class="Bound">x</a> <a id="21094" href="plfa.part2.Lambda.html#4083" class="InductiveConstructor Operator">⇒</a> <a id="21096" href="plfa.part2.Lambda.html#21044" class="Bound">M</a> <a id="21098" href="plfa.part2.Lambda.html#20189" class="Datatype Operator">—→</a> <a id="21101" href="plfa.part2.Lambda.html#21044" class="Bound">M</a> <a id="21103" href="plfa.part2.Lambda.html#15548" class="Function Operator">[</a> <a id="21105" href="plfa.part2.Lambda.html#21042" class="Bound">x</a> <a id="21107" href="plfa.part2.Lambda.html#15548" class="Function Operator">:=</a> <a id="21110" href="plfa.part2.Lambda.html#4083" class="InductiveConstructor Operator">μ</a> <a id="21112" href="plfa.part2.Lambda.html#21042" class="Bound">x</a> <a id="21114" href="plfa.part2.Lambda.html#4083" class="InductiveConstructor Operator">⇒</a> <a id="21116" href="plfa.part2.Lambda.html#21044" class="Bound">M</a> <a id="21118" href="plfa.part2.Lambda.html#15548" class="Function Operator">]</a>
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
{% raw %}<pre class="Agda"><a id="23114" class="Keyword">infix</a>  <a id="23121" class="Number">2</a> <a id="23123" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23179" class="Datatype Operator">_—↠_</a>
<a id="23128" class="Keyword">infix</a>  <a id="23135" class="Number">1</a> <a id="23137" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23329" class="Function Operator">begin_</a>
<a id="23144" class="Keyword">infixr</a> <a id="23151" class="Number">2</a> <a id="23153" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23253" class="InductiveConstructor Operator">_—→⟨_⟩_</a>
<a id="23161" class="Keyword">infix</a>  <a id="23168" class="Number">3</a> <a id="23170" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23212" class="InductiveConstructor Operator">_∎</a>

<a id="23174" class="Keyword">data</a> <a id="_—↠_"></a><a id="23179" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23179" class="Datatype Operator">_—↠_</a> <a id="23184" class="Symbol">:</a> <a id="23186" href="plfa.part2.Lambda.html#3796" class="Datatype">Term</a> <a id="23191" class="Symbol">→</a> <a id="23193" href="plfa.part2.Lambda.html#3796" class="Datatype">Term</a> <a id="23198" class="Symbol">→</a> <a id="23200" class="PrimitiveType">Set</a> <a id="23204" class="Keyword">where</a>
  <a id="_—↠_._∎"></a><a id="23212" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23212" class="InductiveConstructor Operator">_∎</a> <a id="23215" class="Symbol">:</a> <a id="23217" class="Symbol">∀</a> <a id="23219" href="plfa.part2.Lambda.html#23219" class="Bound">M</a>
      <a id="23227" class="Comment">---------</a>
    <a id="23241" class="Symbol">→</a> <a id="23243" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23219" class="Bound">M</a> <a id="23245" href="plfa.part2.Lambda.html#23179" class="Datatype Operator">—↠</a> <a id="23248" href="plfa.part2.Lambda.html#23219" class="Bound">M</a>

  <a id="_—↠_._—→⟨_⟩_"></a><a id="23253" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23253" class="InductiveConstructor Operator">_—→⟨_⟩_</a> <a id="23261" class="Symbol">:</a> <a id="23263" class="Symbol">∀</a> <a id="23265" href="plfa.part2.Lambda.html#23265" class="Bound">L</a> <a id="23267" class="Symbol">{</a><a id="23268" href="plfa.part2.Lambda.html#23268" class="Bound">M</a> <a id="23270" href="plfa.part2.Lambda.html#23270" class="Bound">N</a><a id="23271" class="Symbol">}</a>
    <a id="23277" class="Symbol">→</a> <a id="23279" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23265" class="Bound">L</a> <a id="23281" href="plfa.part2.Lambda.html#20189" class="Datatype Operator">—→</a> <a id="23284" href="plfa.part2.Lambda.html#23268" class="Bound">M</a>
    <a id="23290" class="Symbol">→</a> <a id="23292" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23268" class="Bound">M</a> <a id="23294" href="plfa.part2.Lambda.html#23179" class="Datatype Operator">—↠</a> <a id="23297" href="plfa.part2.Lambda.html#23270" class="Bound">N</a>
      <a id="23305" class="Comment">---------</a>
    <a id="23319" class="Symbol">→</a> <a id="23321" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23265" class="Bound">L</a> <a id="23323" href="plfa.part2.Lambda.html#23179" class="Datatype Operator">—↠</a> <a id="23326" href="plfa.part2.Lambda.html#23270" class="Bound">N</a>

<a id="begin_"></a><a id="23329" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23329" class="Function Operator">begin_</a> <a id="23336" class="Symbol">:</a> <a id="23338" class="Symbol">∀</a> <a id="23340" class="Symbol">{</a><a id="23341" href="plfa.part2.Lambda.html#23341" class="Bound">M</a> <a id="23343" href="plfa.part2.Lambda.html#23343" class="Bound">N</a><a id="23344" class="Symbol">}</a>
  <a id="23348" class="Symbol">→</a> <a id="23350" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23341" class="Bound">M</a> <a id="23352" href="plfa.part2.Lambda.html#23179" class="Datatype Operator">—↠</a> <a id="23355" href="plfa.part2.Lambda.html#23343" class="Bound">N</a>
    <a id="23361" class="Comment">------</a>
  <a id="23370" class="Symbol">→</a> <a id="23372" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23341" class="Bound">M</a> <a id="23374" href="plfa.part2.Lambda.html#23179" class="Datatype Operator">—↠</a> <a id="23377" href="plfa.part2.Lambda.html#23343" class="Bound">N</a>
<a id="23379" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23329" class="Function Operator">begin</a> <a id="23385" href="plfa.part2.Lambda.html#23385" class="Bound">M—↠N</a> <a id="23390" class="Symbol">=</a> <a id="23392" href="plfa.part2.Lambda.html#23385" class="Bound">M—↠N</a>
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
{% raw %}<pre class="Agda"><a id="24075" class="Keyword">data</a> <a id="_—↠′_"></a><a id="24080" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#24080" class="Datatype Operator">_—↠′_</a> <a id="24086" class="Symbol">:</a> <a id="24088" href="plfa.part2.Lambda.html#3796" class="Datatype">Term</a> <a id="24093" class="Symbol">→</a> <a id="24095" href="plfa.part2.Lambda.html#3796" class="Datatype">Term</a> <a id="24100" class="Symbol">→</a> <a id="24102" class="PrimitiveType">Set</a> <a id="24106" class="Keyword">where</a>

  <a id="_—↠′_.step′"></a><a id="24115" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#24115" class="InductiveConstructor">step′</a> <a id="24121" class="Symbol">:</a> <a id="24123" class="Symbol">∀</a> <a id="24125" class="Symbol">{</a><a id="24126" href="plfa.part2.Lambda.html#24126" class="Bound">M</a> <a id="24128" href="plfa.part2.Lambda.html#24128" class="Bound">N</a><a id="24129" class="Symbol">}</a>
    <a id="24135" class="Symbol">→</a> <a id="24137" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#24126" class="Bound">M</a> <a id="24139" href="plfa.part2.Lambda.html#20189" class="Datatype Operator">—→</a> <a id="24142" href="plfa.part2.Lambda.html#24128" class="Bound">N</a>
      <a id="24150" class="Comment">-------</a>
    <a id="24162" class="Symbol">→</a> <a id="24164" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#24126" class="Bound">M</a> <a id="24166" href="plfa.part2.Lambda.html#24080" class="Datatype Operator">—↠′</a> <a id="24170" href="plfa.part2.Lambda.html#24128" class="Bound">N</a>

  <a id="_—↠′_.refl′"></a><a id="24175" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#24175" class="InductiveConstructor">refl′</a> <a id="24181" class="Symbol">:</a> <a id="24183" class="Symbol">∀</a> <a id="24185" class="Symbol">{</a><a id="24186" href="plfa.part2.Lambda.html#24186" class="Bound">M</a><a id="24187" class="Symbol">}</a>
      <a id="24195" class="Comment">-------</a>
    <a id="24207" class="Symbol">→</a> <a id="24209" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#24186" class="Bound">M</a> <a id="24211" href="plfa.part2.Lambda.html#24080" class="Datatype Operator">—↠′</a> <a id="24215" href="plfa.part2.Lambda.html#24186" class="Bound">M</a>

  <a id="_—↠′_.trans′"></a><a id="24220" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#24220" class="InductiveConstructor">trans′</a> <a id="24227" class="Symbol">:</a> <a id="24229" class="Symbol">∀</a> <a id="24231" class="Symbol">{</a><a id="24232" href="plfa.part2.Lambda.html#24232" class="Bound">L</a> <a id="24234" href="plfa.part2.Lambda.html#24234" class="Bound">M</a> <a id="24236" href="plfa.part2.Lambda.html#24236" class="Bound">N</a><a id="24237" class="Symbol">}</a>
    <a id="24243" class="Symbol">→</a> <a id="24245" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#24232" class="Bound">L</a> <a id="24247" href="plfa.part2.Lambda.html#24080" class="Datatype Operator">—↠′</a> <a id="24251" href="plfa.part2.Lambda.html#24234" class="Bound">M</a>
    <a id="24257" class="Symbol">→</a> <a id="24259" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#24234" class="Bound">M</a> <a id="24261" href="plfa.part2.Lambda.html#24080" class="Datatype Operator">—↠′</a> <a id="24265" href="plfa.part2.Lambda.html#24236" class="Bound">N</a>
      <a id="24273" class="Comment">-------</a>
    <a id="24285" class="Symbol">→</a> <a id="24287" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#24232" class="Bound">L</a> <a id="24289" href="plfa.part2.Lambda.html#24080" class="Datatype Operator">—↠′</a> <a id="24293" href="plfa.part2.Lambda.html#24236" class="Bound">N</a>
</pre>{% endraw %}The three constructors specify, respectively, that `—↠′` includes `—→`
and is reflexive and transitive.  A good exercise is to show that
the two definitions are equivalent (indeed, one embeds in the other).

#### Exercise `—↠≲—↠′` (practice)

Show that the first notion of reflexive and transitive closure
above embeds into the second. Why are they not isomorphic?

{% raw %}<pre class="Agda"><a id="24669" class="Comment">-- Your code goes here</a>
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
{% raw %}<pre class="Agda"><a id="26239" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#26239" class="Function">_</a> <a id="26241" class="Symbol">:</a> <a id="26243" href="plfa.part2.Lambda.html#5773" class="Function">twoᶜ</a> <a id="26248" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="26250" href="plfa.part2.Lambda.html#5938" class="Function">sucᶜ</a> <a id="26255" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="26257" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a> <a id="26263" href="plfa.part2.Lambda.html#23179" class="Datatype Operator">—↠</a> <a id="26266" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="26271" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="26276" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a>
<a id="26282" class="Symbol">_</a> <a id="26284" class="Symbol">=</a>
  <a id="26288" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23329" class="Function Operator">begin</a>
    <a id="26298" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#5773" class="Function">twoᶜ</a> <a id="26303" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="26305" href="plfa.part2.Lambda.html#5938" class="Function">sucᶜ</a> <a id="26310" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="26312" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a>
  <a id="26320" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23253" class="InductiveConstructor Operator">—→⟨</a> <a id="26324" href="plfa.part2.Lambda.html#20223" class="InductiveConstructor">ξ-·₁</a> <a id="26329" class="Symbol">(</a><a id="26330" href="plfa.part2.Lambda.html#20399" class="InductiveConstructor">β-ƛ</a> <a id="26334" href="plfa.part2.Lambda.html#12193" class="InductiveConstructor">V-ƛ</a><a id="26337" class="Symbol">)</a> <a id="26339" href="plfa.part2.Lambda.html#23253" class="InductiveConstructor Operator">⟩</a>
    <a id="26345" class="Symbol">(</a><a id="26346" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3854" class="InductiveConstructor Operator">ƛ</a> <a id="26348" class="String">&quot;z&quot;</a> <a id="26352" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a> <a id="26354" href="plfa.part2.Lambda.html#5938" class="Function">sucᶜ</a> <a id="26359" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="26361" class="Symbol">(</a><a id="26362" href="plfa.part2.Lambda.html#5938" class="Function">sucᶜ</a> <a id="26367" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="26369" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="26371" class="String">&quot;z&quot;</a><a id="26374" class="Symbol">))</a> <a id="26377" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="26379" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a>
  <a id="26387" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23253" class="InductiveConstructor Operator">—→⟨</a> <a id="26391" href="plfa.part2.Lambda.html#20399" class="InductiveConstructor">β-ƛ</a> <a id="26395" href="plfa.part2.Lambda.html#12254" class="InductiveConstructor">V-zero</a> <a id="26402" href="plfa.part2.Lambda.html#23253" class="InductiveConstructor Operator">⟩</a>
    <a id="26408" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#5938" class="Function">sucᶜ</a> <a id="26413" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="26415" class="Symbol">(</a><a id="26416" href="plfa.part2.Lambda.html#5938" class="Function">sucᶜ</a> <a id="26421" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="26423" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a><a id="26428" class="Symbol">)</a>
  <a id="26432" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23253" class="InductiveConstructor Operator">—→⟨</a> <a id="26436" href="plfa.part2.Lambda.html#20304" class="InductiveConstructor">ξ-·₂</a> <a id="26441" href="plfa.part2.Lambda.html#12193" class="InductiveConstructor">V-ƛ</a> <a id="26445" class="Symbol">(</a><a id="26446" href="plfa.part2.Lambda.html#20399" class="InductiveConstructor">β-ƛ</a> <a id="26450" href="plfa.part2.Lambda.html#12254" class="InductiveConstructor">V-zero</a><a id="26456" class="Symbol">)</a> <a id="26458" href="plfa.part2.Lambda.html#23253" class="InductiveConstructor Operator">⟩</a>
    <a id="26464" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#5938" class="Function">sucᶜ</a> <a id="26469" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="26471" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="26476" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a>
  <a id="26484" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23253" class="InductiveConstructor Operator">—→⟨</a> <a id="26488" href="plfa.part2.Lambda.html#20399" class="InductiveConstructor">β-ƛ</a> <a id="26492" class="Symbol">(</a><a id="26493" href="plfa.part2.Lambda.html#12302" class="InductiveConstructor">V-suc</a> <a id="26499" href="plfa.part2.Lambda.html#12254" class="InductiveConstructor">V-zero</a><a id="26505" class="Symbol">)</a> <a id="26507" href="plfa.part2.Lambda.html#23253" class="InductiveConstructor Operator">⟩</a>
    <a id="26513" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3982" class="InductiveConstructor Operator">`suc</a> <a id="26518" class="Symbol">(</a><a id="26519" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="26524" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a><a id="26529" class="Symbol">)</a>
  <a id="26533" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23212" class="InductiveConstructor Operator">∎</a>
</pre>{% endraw %}
Here is a sample reduction demonstrating that two plus two is four:
{% raw %}<pre class="Agda"><a id="26612" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#26612" class="Function">_</a> <a id="26614" class="Symbol">:</a> <a id="26616" href="plfa.part2.Lambda.html#4558" class="Function">plus</a> <a id="26621" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="26623" href="plfa.part2.Lambda.html#4524" class="Function">two</a> <a id="26627" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="26629" href="plfa.part2.Lambda.html#4524" class="Function">two</a> <a id="26633" href="plfa.part2.Lambda.html#23179" class="Datatype Operator">—↠</a> <a id="26636" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="26641" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="26646" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="26651" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="26656" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a>
<a id="26662" class="Symbol">_</a> <a id="26664" class="Symbol">=</a>
  <a id="26668" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23329" class="Function Operator">begin</a>
    <a id="26678" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#4558" class="Function">plus</a> <a id="26683" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="26685" href="plfa.part2.Lambda.html#4524" class="Function">two</a> <a id="26689" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="26691" href="plfa.part2.Lambda.html#4524" class="Function">two</a>
  <a id="26697" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23253" class="InductiveConstructor Operator">—→⟨</a> <a id="26701" href="plfa.part2.Lambda.html#20223" class="InductiveConstructor">ξ-·₁</a> <a id="26706" class="Symbol">(</a><a id="26707" href="plfa.part2.Lambda.html#20223" class="InductiveConstructor">ξ-·₁</a> <a id="26712" href="plfa.part2.Lambda.html#21033" class="InductiveConstructor">β-μ</a><a id="26715" class="Symbol">)</a> <a id="26717" href="plfa.part2.Lambda.html#23253" class="InductiveConstructor Operator">⟩</a>
    <a id="26723" class="Symbol">(</a><a id="26724" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3854" class="InductiveConstructor Operator">ƛ</a> <a id="26726" class="String">&quot;m&quot;</a> <a id="26730" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a> <a id="26732" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">ƛ</a> <a id="26734" class="String">&quot;n&quot;</a> <a id="26738" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a>
      <a id="26746" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#4023" class="InductiveConstructor Operator">case</a> <a id="26751" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="26753" class="String">&quot;m&quot;</a> <a id="26757" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">[zero⇒</a> <a id="26764" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="26766" class="String">&quot;n&quot;</a> <a id="26770" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">|suc</a> <a id="26775" class="String">&quot;m&quot;</a> <a id="26779" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">⇒</a> <a id="26781" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="26786" class="Symbol">(</a><a id="26787" href="plfa.part2.Lambda.html#4558" class="Function">plus</a> <a id="26792" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="26794" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="26796" class="String">&quot;m&quot;</a> <a id="26800" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="26802" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="26804" class="String">&quot;n&quot;</a><a id="26807" class="Symbol">)</a> <a id="26809" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">]</a><a id="26810" class="Symbol">)</a>
        <a id="26820" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3900" class="InductiveConstructor Operator">·</a> <a id="26822" href="plfa.part2.Lambda.html#4524" class="Function">two</a> <a id="26826" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="26828" href="plfa.part2.Lambda.html#4524" class="Function">two</a>
  <a id="26834" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23253" class="InductiveConstructor Operator">—→⟨</a> <a id="26838" href="plfa.part2.Lambda.html#20223" class="InductiveConstructor">ξ-·₁</a> <a id="26843" class="Symbol">(</a><a id="26844" href="plfa.part2.Lambda.html#20399" class="InductiveConstructor">β-ƛ</a> <a id="26848" class="Symbol">(</a><a id="26849" href="plfa.part2.Lambda.html#12302" class="InductiveConstructor">V-suc</a> <a id="26855" class="Symbol">(</a><a id="26856" href="plfa.part2.Lambda.html#12302" class="InductiveConstructor">V-suc</a> <a id="26862" href="plfa.part2.Lambda.html#12254" class="InductiveConstructor">V-zero</a><a id="26868" class="Symbol">)))</a> <a id="26872" href="plfa.part2.Lambda.html#23253" class="InductiveConstructor Operator">⟩</a>
    <a id="26878" class="Symbol">(</a><a id="26879" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3854" class="InductiveConstructor Operator">ƛ</a> <a id="26881" class="String">&quot;n&quot;</a> <a id="26885" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a>
      <a id="26893" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#4023" class="InductiveConstructor Operator">case</a> <a id="26898" href="plfa.part2.Lambda.html#4524" class="Function">two</a> <a id="26902" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">[zero⇒</a> <a id="26909" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="26911" class="String">&quot;n&quot;</a> <a id="26915" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">|suc</a> <a id="26920" class="String">&quot;m&quot;</a> <a id="26924" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">⇒</a> <a id="26926" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="26931" class="Symbol">(</a><a id="26932" href="plfa.part2.Lambda.html#4558" class="Function">plus</a> <a id="26937" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="26939" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="26941" class="String">&quot;m&quot;</a> <a id="26945" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="26947" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="26949" class="String">&quot;n&quot;</a><a id="26952" class="Symbol">)</a> <a id="26954" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">]</a><a id="26955" class="Symbol">)</a>
         <a id="26966" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3900" class="InductiveConstructor Operator">·</a> <a id="26968" href="plfa.part2.Lambda.html#4524" class="Function">two</a>
  <a id="26974" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23253" class="InductiveConstructor Operator">—→⟨</a> <a id="26978" href="plfa.part2.Lambda.html#20399" class="InductiveConstructor">β-ƛ</a> <a id="26982" class="Symbol">(</a><a id="26983" href="plfa.part2.Lambda.html#12302" class="InductiveConstructor">V-suc</a> <a id="26989" class="Symbol">(</a><a id="26990" href="plfa.part2.Lambda.html#12302" class="InductiveConstructor">V-suc</a> <a id="26996" href="plfa.part2.Lambda.html#12254" class="InductiveConstructor">V-zero</a><a id="27002" class="Symbol">))</a> <a id="27005" href="plfa.part2.Lambda.html#23253" class="InductiveConstructor Operator">⟩</a>
    <a id="27011" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#4023" class="InductiveConstructor Operator">case</a> <a id="27016" href="plfa.part2.Lambda.html#4524" class="Function">two</a> <a id="27020" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">[zero⇒</a> <a id="27027" href="plfa.part2.Lambda.html#4524" class="Function">two</a> <a id="27031" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">|suc</a> <a id="27036" class="String">&quot;m&quot;</a> <a id="27040" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">⇒</a> <a id="27042" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="27047" class="Symbol">(</a><a id="27048" href="plfa.part2.Lambda.html#4558" class="Function">plus</a> <a id="27053" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="27055" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="27057" class="String">&quot;m&quot;</a> <a id="27061" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="27063" href="plfa.part2.Lambda.html#4524" class="Function">two</a><a id="27066" class="Symbol">)</a> <a id="27068" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">]</a>
  <a id="27072" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23253" class="InductiveConstructor Operator">—→⟨</a> <a id="27076" href="plfa.part2.Lambda.html#20882" class="InductiveConstructor">β-suc</a> <a id="27082" class="Symbol">(</a><a id="27083" href="plfa.part2.Lambda.html#12302" class="InductiveConstructor">V-suc</a> <a id="27089" href="plfa.part2.Lambda.html#12254" class="InductiveConstructor">V-zero</a><a id="27095" class="Symbol">)</a> <a id="27097" href="plfa.part2.Lambda.html#23253" class="InductiveConstructor Operator">⟩</a>
    <a id="27103" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3982" class="InductiveConstructor Operator">`suc</a> <a id="27108" class="Symbol">(</a><a id="27109" href="plfa.part2.Lambda.html#4558" class="Function">plus</a> <a id="27114" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="27116" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="27121" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a> <a id="27127" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="27129" href="plfa.part2.Lambda.html#4524" class="Function">two</a><a id="27132" class="Symbol">)</a>
  <a id="27136" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23253" class="InductiveConstructor Operator">—→⟨</a> <a id="27140" href="plfa.part2.Lambda.html#20505" class="InductiveConstructor">ξ-suc</a> <a id="27146" class="Symbol">(</a><a id="27147" href="plfa.part2.Lambda.html#20223" class="InductiveConstructor">ξ-·₁</a> <a id="27152" class="Symbol">(</a><a id="27153" href="plfa.part2.Lambda.html#20223" class="InductiveConstructor">ξ-·₁</a> <a id="27158" href="plfa.part2.Lambda.html#21033" class="InductiveConstructor">β-μ</a><a id="27161" class="Symbol">))</a> <a id="27164" href="plfa.part2.Lambda.html#23253" class="InductiveConstructor Operator">⟩</a>
    <a id="27170" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3982" class="InductiveConstructor Operator">`suc</a> <a id="27175" class="Symbol">((</a><a id="27177" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">ƛ</a> <a id="27179" class="String">&quot;m&quot;</a> <a id="27183" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a> <a id="27185" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">ƛ</a> <a id="27187" class="String">&quot;n&quot;</a> <a id="27191" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a>
      <a id="27199" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#4023" class="InductiveConstructor Operator">case</a> <a id="27204" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="27206" class="String">&quot;m&quot;</a> <a id="27210" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">[zero⇒</a> <a id="27217" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="27219" class="String">&quot;n&quot;</a> <a id="27223" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">|suc</a> <a id="27228" class="String">&quot;m&quot;</a> <a id="27232" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">⇒</a> <a id="27234" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="27239" class="Symbol">(</a><a id="27240" href="plfa.part2.Lambda.html#4558" class="Function">plus</a> <a id="27245" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="27247" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="27249" class="String">&quot;m&quot;</a> <a id="27253" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="27255" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="27257" class="String">&quot;n&quot;</a><a id="27260" class="Symbol">)</a> <a id="27262" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">]</a><a id="27263" class="Symbol">)</a>
        <a id="27273" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3900" class="InductiveConstructor Operator">·</a> <a id="27275" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="27280" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a> <a id="27286" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="27288" href="plfa.part2.Lambda.html#4524" class="Function">two</a><a id="27291" class="Symbol">)</a>
  <a id="27295" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23253" class="InductiveConstructor Operator">—→⟨</a> <a id="27299" href="plfa.part2.Lambda.html#20505" class="InductiveConstructor">ξ-suc</a> <a id="27305" class="Symbol">(</a><a id="27306" href="plfa.part2.Lambda.html#20223" class="InductiveConstructor">ξ-·₁</a> <a id="27311" class="Symbol">(</a><a id="27312" href="plfa.part2.Lambda.html#20399" class="InductiveConstructor">β-ƛ</a> <a id="27316" class="Symbol">(</a><a id="27317" href="plfa.part2.Lambda.html#12302" class="InductiveConstructor">V-suc</a> <a id="27323" href="plfa.part2.Lambda.html#12254" class="InductiveConstructor">V-zero</a><a id="27329" class="Symbol">)))</a> <a id="27333" href="plfa.part2.Lambda.html#23253" class="InductiveConstructor Operator">⟩</a>
    <a id="27339" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3982" class="InductiveConstructor Operator">`suc</a> <a id="27344" class="Symbol">((</a><a id="27346" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">ƛ</a> <a id="27348" class="String">&quot;n&quot;</a> <a id="27352" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a>
      <a id="27360" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#4023" class="InductiveConstructor Operator">case</a> <a id="27365" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="27370" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a> <a id="27376" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">[zero⇒</a> <a id="27383" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="27385" class="String">&quot;n&quot;</a> <a id="27389" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">|suc</a> <a id="27394" class="String">&quot;m&quot;</a> <a id="27398" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">⇒</a> <a id="27400" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="27405" class="Symbol">(</a><a id="27406" href="plfa.part2.Lambda.html#4558" class="Function">plus</a> <a id="27411" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="27413" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="27415" class="String">&quot;m&quot;</a> <a id="27419" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="27421" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="27423" class="String">&quot;n&quot;</a><a id="27426" class="Symbol">)</a> <a id="27428" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">]</a><a id="27429" class="Symbol">)</a>
        <a id="27439" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3900" class="InductiveConstructor Operator">·</a> <a id="27441" href="plfa.part2.Lambda.html#4524" class="Function">two</a><a id="27444" class="Symbol">)</a>
  <a id="27448" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23253" class="InductiveConstructor Operator">—→⟨</a> <a id="27452" href="plfa.part2.Lambda.html#20505" class="InductiveConstructor">ξ-suc</a> <a id="27458" class="Symbol">(</a><a id="27459" href="plfa.part2.Lambda.html#20399" class="InductiveConstructor">β-ƛ</a> <a id="27463" class="Symbol">(</a><a id="27464" href="plfa.part2.Lambda.html#12302" class="InductiveConstructor">V-suc</a> <a id="27470" class="Symbol">(</a><a id="27471" href="plfa.part2.Lambda.html#12302" class="InductiveConstructor">V-suc</a> <a id="27477" href="plfa.part2.Lambda.html#12254" class="InductiveConstructor">V-zero</a><a id="27483" class="Symbol">)))</a> <a id="27487" href="plfa.part2.Lambda.html#23253" class="InductiveConstructor Operator">⟩</a>
    <a id="27493" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3982" class="InductiveConstructor Operator">`suc</a> <a id="27498" class="Symbol">(</a><a id="27499" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">case</a> <a id="27504" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="27509" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a> <a id="27515" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">[zero⇒</a> <a id="27522" href="plfa.part2.Lambda.html#4524" class="Function">two</a> <a id="27526" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">|suc</a> <a id="27531" class="String">&quot;m&quot;</a> <a id="27535" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">⇒</a> <a id="27537" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="27542" class="Symbol">(</a><a id="27543" href="plfa.part2.Lambda.html#4558" class="Function">plus</a> <a id="27548" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="27550" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="27552" class="String">&quot;m&quot;</a> <a id="27556" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="27558" href="plfa.part2.Lambda.html#4524" class="Function">two</a><a id="27561" class="Symbol">)</a> <a id="27563" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">]</a><a id="27564" class="Symbol">)</a>
  <a id="27568" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23253" class="InductiveConstructor Operator">—→⟨</a> <a id="27572" href="plfa.part2.Lambda.html#20505" class="InductiveConstructor">ξ-suc</a> <a id="27578" class="Symbol">(</a><a id="27579" href="plfa.part2.Lambda.html#20882" class="InductiveConstructor">β-suc</a> <a id="27585" href="plfa.part2.Lambda.html#12254" class="InductiveConstructor">V-zero</a><a id="27591" class="Symbol">)</a> <a id="27593" href="plfa.part2.Lambda.html#23253" class="InductiveConstructor Operator">⟩</a>
    <a id="27599" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3982" class="InductiveConstructor Operator">`suc</a> <a id="27604" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="27609" class="Symbol">(</a><a id="27610" href="plfa.part2.Lambda.html#4558" class="Function">plus</a> <a id="27615" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="27617" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a> <a id="27623" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="27625" href="plfa.part2.Lambda.html#4524" class="Function">two</a><a id="27628" class="Symbol">)</a>
  <a id="27632" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23253" class="InductiveConstructor Operator">—→⟨</a> <a id="27636" href="plfa.part2.Lambda.html#20505" class="InductiveConstructor">ξ-suc</a> <a id="27642" class="Symbol">(</a><a id="27643" href="plfa.part2.Lambda.html#20505" class="InductiveConstructor">ξ-suc</a> <a id="27649" class="Symbol">(</a><a id="27650" href="plfa.part2.Lambda.html#20223" class="InductiveConstructor">ξ-·₁</a> <a id="27655" class="Symbol">(</a><a id="27656" href="plfa.part2.Lambda.html#20223" class="InductiveConstructor">ξ-·₁</a> <a id="27661" href="plfa.part2.Lambda.html#21033" class="InductiveConstructor">β-μ</a><a id="27664" class="Symbol">)))</a> <a id="27668" href="plfa.part2.Lambda.html#23253" class="InductiveConstructor Operator">⟩</a>
    <a id="27674" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3982" class="InductiveConstructor Operator">`suc</a> <a id="27679" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="27684" class="Symbol">((</a><a id="27686" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">ƛ</a> <a id="27688" class="String">&quot;m&quot;</a> <a id="27692" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a> <a id="27694" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">ƛ</a> <a id="27696" class="String">&quot;n&quot;</a> <a id="27700" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a>
      <a id="27708" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#4023" class="InductiveConstructor Operator">case</a> <a id="27713" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="27715" class="String">&quot;m&quot;</a> <a id="27719" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">[zero⇒</a> <a id="27726" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="27728" class="String">&quot;n&quot;</a> <a id="27732" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">|suc</a> <a id="27737" class="String">&quot;m&quot;</a> <a id="27741" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">⇒</a> <a id="27743" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="27748" class="Symbol">(</a><a id="27749" href="plfa.part2.Lambda.html#4558" class="Function">plus</a> <a id="27754" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="27756" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="27758" class="String">&quot;m&quot;</a> <a id="27762" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="27764" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="27766" class="String">&quot;n&quot;</a><a id="27769" class="Symbol">)</a> <a id="27771" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">]</a><a id="27772" class="Symbol">)</a>
        <a id="27782" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3900" class="InductiveConstructor Operator">·</a> <a id="27784" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a> <a id="27790" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="27792" href="plfa.part2.Lambda.html#4524" class="Function">two</a><a id="27795" class="Symbol">)</a>
  <a id="27799" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23253" class="InductiveConstructor Operator">—→⟨</a> <a id="27803" href="plfa.part2.Lambda.html#20505" class="InductiveConstructor">ξ-suc</a> <a id="27809" class="Symbol">(</a><a id="27810" href="plfa.part2.Lambda.html#20505" class="InductiveConstructor">ξ-suc</a> <a id="27816" class="Symbol">(</a><a id="27817" href="plfa.part2.Lambda.html#20223" class="InductiveConstructor">ξ-·₁</a> <a id="27822" class="Symbol">(</a><a id="27823" href="plfa.part2.Lambda.html#20399" class="InductiveConstructor">β-ƛ</a> <a id="27827" href="plfa.part2.Lambda.html#12254" class="InductiveConstructor">V-zero</a><a id="27833" class="Symbol">)))</a> <a id="27837" href="plfa.part2.Lambda.html#23253" class="InductiveConstructor Operator">⟩</a>
    <a id="27843" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3982" class="InductiveConstructor Operator">`suc</a> <a id="27848" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="27853" class="Symbol">((</a><a id="27855" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">ƛ</a> <a id="27857" class="String">&quot;n&quot;</a> <a id="27861" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a>
      <a id="27869" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#4023" class="InductiveConstructor Operator">case</a> <a id="27874" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a> <a id="27880" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">[zero⇒</a> <a id="27887" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="27889" class="String">&quot;n&quot;</a> <a id="27893" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">|suc</a> <a id="27898" class="String">&quot;m&quot;</a> <a id="27902" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">⇒</a> <a id="27904" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="27909" class="Symbol">(</a><a id="27910" href="plfa.part2.Lambda.html#4558" class="Function">plus</a> <a id="27915" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="27917" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="27919" class="String">&quot;m&quot;</a> <a id="27923" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="27925" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="27927" class="String">&quot;n&quot;</a><a id="27930" class="Symbol">)</a> <a id="27932" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">]</a><a id="27933" class="Symbol">)</a>
        <a id="27943" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3900" class="InductiveConstructor Operator">·</a> <a id="27945" href="plfa.part2.Lambda.html#4524" class="Function">two</a><a id="27948" class="Symbol">)</a>
  <a id="27952" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23253" class="InductiveConstructor Operator">—→⟨</a> <a id="27956" href="plfa.part2.Lambda.html#20505" class="InductiveConstructor">ξ-suc</a> <a id="27962" class="Symbol">(</a><a id="27963" href="plfa.part2.Lambda.html#20505" class="InductiveConstructor">ξ-suc</a> <a id="27969" class="Symbol">(</a><a id="27970" href="plfa.part2.Lambda.html#20399" class="InductiveConstructor">β-ƛ</a> <a id="27974" class="Symbol">(</a><a id="27975" href="plfa.part2.Lambda.html#12302" class="InductiveConstructor">V-suc</a> <a id="27981" class="Symbol">(</a><a id="27982" href="plfa.part2.Lambda.html#12302" class="InductiveConstructor">V-suc</a> <a id="27988" href="plfa.part2.Lambda.html#12254" class="InductiveConstructor">V-zero</a><a id="27994" class="Symbol">))))</a> <a id="27999" href="plfa.part2.Lambda.html#23253" class="InductiveConstructor Operator">⟩</a>
    <a id="28005" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3982" class="InductiveConstructor Operator">`suc</a> <a id="28010" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="28015" class="Symbol">(</a><a id="28016" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">case</a> <a id="28021" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a> <a id="28027" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">[zero⇒</a> <a id="28034" href="plfa.part2.Lambda.html#4524" class="Function">two</a> <a id="28038" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">|suc</a> <a id="28043" class="String">&quot;m&quot;</a> <a id="28047" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">⇒</a> <a id="28049" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="28054" class="Symbol">(</a><a id="28055" href="plfa.part2.Lambda.html#4558" class="Function">plus</a> <a id="28060" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="28062" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="28064" class="String">&quot;m&quot;</a> <a id="28068" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="28070" href="plfa.part2.Lambda.html#4524" class="Function">two</a><a id="28073" class="Symbol">)</a> <a id="28075" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">]</a><a id="28076" class="Symbol">)</a>
  <a id="28080" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23253" class="InductiveConstructor Operator">—→⟨</a> <a id="28084" href="plfa.part2.Lambda.html#20505" class="InductiveConstructor">ξ-suc</a> <a id="28090" class="Symbol">(</a><a id="28091" href="plfa.part2.Lambda.html#20505" class="InductiveConstructor">ξ-suc</a> <a id="28097" href="plfa.part2.Lambda.html#20769" class="InductiveConstructor">β-zero</a><a id="28103" class="Symbol">)</a> <a id="28105" href="plfa.part2.Lambda.html#23253" class="InductiveConstructor Operator">⟩</a>
    <a id="28111" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3982" class="InductiveConstructor Operator">`suc</a> <a id="28116" class="Symbol">(</a><a id="28117" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="28122" class="Symbol">(</a><a id="28123" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="28128" class="Symbol">(</a><a id="28129" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="28134" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a><a id="28139" class="Symbol">)))</a>
  <a id="28145" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23212" class="InductiveConstructor Operator">∎</a>
</pre>{% endraw %}
And here is a similar sample reduction for Church numerals:
{% raw %}<pre class="Agda"><a id="28216" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#28216" class="Function">_</a> <a id="28218" class="Symbol">:</a> <a id="28220" href="plfa.part2.Lambda.html#5834" class="Function">plusᶜ</a> <a id="28226" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="28228" href="plfa.part2.Lambda.html#5773" class="Function">twoᶜ</a> <a id="28233" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="28235" href="plfa.part2.Lambda.html#5773" class="Function">twoᶜ</a> <a id="28240" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="28242" href="plfa.part2.Lambda.html#5938" class="Function">sucᶜ</a> <a id="28247" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="28249" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a> <a id="28255" href="plfa.part2.Lambda.html#23179" class="Datatype Operator">—↠</a> <a id="28258" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="28263" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="28268" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="28273" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="28278" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a>
<a id="28284" class="Symbol">_</a> <a id="28286" class="Symbol">=</a>
  <a id="28290" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23329" class="Function Operator">begin</a>
    <a id="28300" class="Symbol">(</a><a id="28301" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3854" class="InductiveConstructor Operator">ƛ</a> <a id="28303" class="String">&quot;m&quot;</a> <a id="28307" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a> <a id="28309" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">ƛ</a> <a id="28311" class="String">&quot;n&quot;</a> <a id="28315" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a> <a id="28317" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">ƛ</a> <a id="28319" class="String">&quot;s&quot;</a> <a id="28323" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a> <a id="28325" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">ƛ</a> <a id="28327" class="String">&quot;z&quot;</a> <a id="28331" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a> <a id="28333" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="28335" class="String">&quot;m&quot;</a> <a id="28339" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="28341" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="28343" class="String">&quot;s&quot;</a> <a id="28347" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="28349" class="Symbol">(</a><a id="28350" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="28352" class="String">&quot;n&quot;</a> <a id="28356" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="28358" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="28360" class="String">&quot;s&quot;</a> <a id="28364" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="28366" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="28368" class="String">&quot;z&quot;</a><a id="28371" class="Symbol">))</a>
      <a id="28380" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3900" class="InductiveConstructor Operator">·</a> <a id="28382" href="plfa.part2.Lambda.html#5773" class="Function">twoᶜ</a> <a id="28387" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="28389" href="plfa.part2.Lambda.html#5773" class="Function">twoᶜ</a> <a id="28394" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="28396" href="plfa.part2.Lambda.html#5938" class="Function">sucᶜ</a> <a id="28401" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="28403" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a>
  <a id="28411" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23253" class="InductiveConstructor Operator">—→⟨</a> <a id="28415" href="plfa.part2.Lambda.html#20223" class="InductiveConstructor">ξ-·₁</a> <a id="28420" class="Symbol">(</a><a id="28421" href="plfa.part2.Lambda.html#20223" class="InductiveConstructor">ξ-·₁</a> <a id="28426" class="Symbol">(</a><a id="28427" href="plfa.part2.Lambda.html#20223" class="InductiveConstructor">ξ-·₁</a> <a id="28432" class="Symbol">(</a><a id="28433" href="plfa.part2.Lambda.html#20399" class="InductiveConstructor">β-ƛ</a> <a id="28437" href="plfa.part2.Lambda.html#12193" class="InductiveConstructor">V-ƛ</a><a id="28440" class="Symbol">)))</a> <a id="28444" href="plfa.part2.Lambda.html#23253" class="InductiveConstructor Operator">⟩</a>
    <a id="28450" class="Symbol">(</a><a id="28451" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3854" class="InductiveConstructor Operator">ƛ</a> <a id="28453" class="String">&quot;n&quot;</a> <a id="28457" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a> <a id="28459" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">ƛ</a> <a id="28461" class="String">&quot;s&quot;</a> <a id="28465" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a> <a id="28467" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">ƛ</a> <a id="28469" class="String">&quot;z&quot;</a> <a id="28473" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a> <a id="28475" href="plfa.part2.Lambda.html#5773" class="Function">twoᶜ</a> <a id="28480" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="28482" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="28484" class="String">&quot;s&quot;</a> <a id="28488" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="28490" class="Symbol">(</a><a id="28491" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="28493" class="String">&quot;n&quot;</a> <a id="28497" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="28499" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="28501" class="String">&quot;s&quot;</a> <a id="28505" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="28507" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="28509" class="String">&quot;z&quot;</a><a id="28512" class="Symbol">))</a>
      <a id="28521" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3900" class="InductiveConstructor Operator">·</a> <a id="28523" href="plfa.part2.Lambda.html#5773" class="Function">twoᶜ</a> <a id="28528" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="28530" href="plfa.part2.Lambda.html#5938" class="Function">sucᶜ</a> <a id="28535" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="28537" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a>
  <a id="28545" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23253" class="InductiveConstructor Operator">—→⟨</a> <a id="28549" href="plfa.part2.Lambda.html#20223" class="InductiveConstructor">ξ-·₁</a> <a id="28554" class="Symbol">(</a><a id="28555" href="plfa.part2.Lambda.html#20223" class="InductiveConstructor">ξ-·₁</a> <a id="28560" class="Symbol">(</a><a id="28561" href="plfa.part2.Lambda.html#20399" class="InductiveConstructor">β-ƛ</a> <a id="28565" href="plfa.part2.Lambda.html#12193" class="InductiveConstructor">V-ƛ</a><a id="28568" class="Symbol">))</a> <a id="28571" href="plfa.part2.Lambda.html#23253" class="InductiveConstructor Operator">⟩</a>
    <a id="28577" class="Symbol">(</a><a id="28578" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3854" class="InductiveConstructor Operator">ƛ</a> <a id="28580" class="String">&quot;s&quot;</a> <a id="28584" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a> <a id="28586" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">ƛ</a> <a id="28588" class="String">&quot;z&quot;</a> <a id="28592" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a> <a id="28594" href="plfa.part2.Lambda.html#5773" class="Function">twoᶜ</a> <a id="28599" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="28601" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="28603" class="String">&quot;s&quot;</a> <a id="28607" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="28609" class="Symbol">(</a><a id="28610" href="plfa.part2.Lambda.html#5773" class="Function">twoᶜ</a> <a id="28615" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="28617" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="28619" class="String">&quot;s&quot;</a> <a id="28623" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="28625" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="28627" class="String">&quot;z&quot;</a><a id="28630" class="Symbol">))</a> <a id="28633" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="28635" href="plfa.part2.Lambda.html#5938" class="Function">sucᶜ</a> <a id="28640" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="28642" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a>
  <a id="28650" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23253" class="InductiveConstructor Operator">—→⟨</a> <a id="28654" href="plfa.part2.Lambda.html#20223" class="InductiveConstructor">ξ-·₁</a> <a id="28659" class="Symbol">(</a><a id="28660" href="plfa.part2.Lambda.html#20399" class="InductiveConstructor">β-ƛ</a> <a id="28664" href="plfa.part2.Lambda.html#12193" class="InductiveConstructor">V-ƛ</a><a id="28667" class="Symbol">)</a> <a id="28669" href="plfa.part2.Lambda.html#23253" class="InductiveConstructor Operator">⟩</a>
    <a id="28675" class="Symbol">(</a><a id="28676" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3854" class="InductiveConstructor Operator">ƛ</a> <a id="28678" class="String">&quot;z&quot;</a> <a id="28682" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a> <a id="28684" href="plfa.part2.Lambda.html#5773" class="Function">twoᶜ</a> <a id="28689" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="28691" href="plfa.part2.Lambda.html#5938" class="Function">sucᶜ</a> <a id="28696" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="28698" class="Symbol">(</a><a id="28699" href="plfa.part2.Lambda.html#5773" class="Function">twoᶜ</a> <a id="28704" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="28706" href="plfa.part2.Lambda.html#5938" class="Function">sucᶜ</a> <a id="28711" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="28713" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="28715" class="String">&quot;z&quot;</a><a id="28718" class="Symbol">))</a> <a id="28721" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="28723" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a>
  <a id="28731" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23253" class="InductiveConstructor Operator">—→⟨</a> <a id="28735" href="plfa.part2.Lambda.html#20399" class="InductiveConstructor">β-ƛ</a> <a id="28739" href="plfa.part2.Lambda.html#12254" class="InductiveConstructor">V-zero</a> <a id="28746" href="plfa.part2.Lambda.html#23253" class="InductiveConstructor Operator">⟩</a>
    <a id="28752" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#5773" class="Function">twoᶜ</a> <a id="28757" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="28759" href="plfa.part2.Lambda.html#5938" class="Function">sucᶜ</a> <a id="28764" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="28766" class="Symbol">(</a><a id="28767" href="plfa.part2.Lambda.html#5773" class="Function">twoᶜ</a> <a id="28772" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="28774" href="plfa.part2.Lambda.html#5938" class="Function">sucᶜ</a> <a id="28779" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="28781" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a><a id="28786" class="Symbol">)</a>
  <a id="28790" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23253" class="InductiveConstructor Operator">—→⟨</a> <a id="28794" href="plfa.part2.Lambda.html#20223" class="InductiveConstructor">ξ-·₁</a> <a id="28799" class="Symbol">(</a><a id="28800" href="plfa.part2.Lambda.html#20399" class="InductiveConstructor">β-ƛ</a> <a id="28804" href="plfa.part2.Lambda.html#12193" class="InductiveConstructor">V-ƛ</a><a id="28807" class="Symbol">)</a> <a id="28809" href="plfa.part2.Lambda.html#23253" class="InductiveConstructor Operator">⟩</a>
    <a id="28815" class="Symbol">(</a><a id="28816" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3854" class="InductiveConstructor Operator">ƛ</a> <a id="28818" class="String">&quot;z&quot;</a> <a id="28822" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a> <a id="28824" href="plfa.part2.Lambda.html#5938" class="Function">sucᶜ</a> <a id="28829" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="28831" class="Symbol">(</a><a id="28832" href="plfa.part2.Lambda.html#5938" class="Function">sucᶜ</a> <a id="28837" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="28839" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="28841" class="String">&quot;z&quot;</a><a id="28844" class="Symbol">))</a> <a id="28847" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="28849" class="Symbol">(</a><a id="28850" href="plfa.part2.Lambda.html#5773" class="Function">twoᶜ</a> <a id="28855" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="28857" href="plfa.part2.Lambda.html#5938" class="Function">sucᶜ</a> <a id="28862" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="28864" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a><a id="28869" class="Symbol">)</a>
  <a id="28873" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23253" class="InductiveConstructor Operator">—→⟨</a> <a id="28877" href="plfa.part2.Lambda.html#20304" class="InductiveConstructor">ξ-·₂</a> <a id="28882" href="plfa.part2.Lambda.html#12193" class="InductiveConstructor">V-ƛ</a> <a id="28886" class="Symbol">(</a><a id="28887" href="plfa.part2.Lambda.html#20223" class="InductiveConstructor">ξ-·₁</a> <a id="28892" class="Symbol">(</a><a id="28893" href="plfa.part2.Lambda.html#20399" class="InductiveConstructor">β-ƛ</a> <a id="28897" href="plfa.part2.Lambda.html#12193" class="InductiveConstructor">V-ƛ</a><a id="28900" class="Symbol">))</a> <a id="28903" href="plfa.part2.Lambda.html#23253" class="InductiveConstructor Operator">⟩</a>
    <a id="28909" class="Symbol">(</a><a id="28910" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3854" class="InductiveConstructor Operator">ƛ</a> <a id="28912" class="String">&quot;z&quot;</a> <a id="28916" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a> <a id="28918" href="plfa.part2.Lambda.html#5938" class="Function">sucᶜ</a> <a id="28923" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="28925" class="Symbol">(</a><a id="28926" href="plfa.part2.Lambda.html#5938" class="Function">sucᶜ</a> <a id="28931" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="28933" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="28935" class="String">&quot;z&quot;</a><a id="28938" class="Symbol">))</a> <a id="28941" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="28943" class="Symbol">((</a><a id="28945" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">ƛ</a> <a id="28947" class="String">&quot;z&quot;</a> <a id="28951" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a> <a id="28953" href="plfa.part2.Lambda.html#5938" class="Function">sucᶜ</a> <a id="28958" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="28960" class="Symbol">(</a><a id="28961" href="plfa.part2.Lambda.html#5938" class="Function">sucᶜ</a> <a id="28966" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="28968" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="28970" class="String">&quot;z&quot;</a><a id="28973" class="Symbol">))</a> <a id="28976" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="28978" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a><a id="28983" class="Symbol">)</a>
  <a id="28987" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23253" class="InductiveConstructor Operator">—→⟨</a> <a id="28991" href="plfa.part2.Lambda.html#20304" class="InductiveConstructor">ξ-·₂</a> <a id="28996" href="plfa.part2.Lambda.html#12193" class="InductiveConstructor">V-ƛ</a> <a id="29000" class="Symbol">(</a><a id="29001" href="plfa.part2.Lambda.html#20399" class="InductiveConstructor">β-ƛ</a> <a id="29005" href="plfa.part2.Lambda.html#12254" class="InductiveConstructor">V-zero</a><a id="29011" class="Symbol">)</a> <a id="29013" href="plfa.part2.Lambda.html#23253" class="InductiveConstructor Operator">⟩</a>
    <a id="29019" class="Symbol">(</a><a id="29020" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3854" class="InductiveConstructor Operator">ƛ</a> <a id="29022" class="String">&quot;z&quot;</a> <a id="29026" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a> <a id="29028" href="plfa.part2.Lambda.html#5938" class="Function">sucᶜ</a> <a id="29033" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="29035" class="Symbol">(</a><a id="29036" href="plfa.part2.Lambda.html#5938" class="Function">sucᶜ</a> <a id="29041" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="29043" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="29045" class="String">&quot;z&quot;</a><a id="29048" class="Symbol">))</a> <a id="29051" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="29053" class="Symbol">(</a><a id="29054" href="plfa.part2.Lambda.html#5938" class="Function">sucᶜ</a> <a id="29059" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="29061" class="Symbol">(</a><a id="29062" href="plfa.part2.Lambda.html#5938" class="Function">sucᶜ</a> <a id="29067" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="29069" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a><a id="29074" class="Symbol">))</a>
  <a id="29079" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23253" class="InductiveConstructor Operator">—→⟨</a> <a id="29083" href="plfa.part2.Lambda.html#20304" class="InductiveConstructor">ξ-·₂</a> <a id="29088" href="plfa.part2.Lambda.html#12193" class="InductiveConstructor">V-ƛ</a> <a id="29092" class="Symbol">(</a><a id="29093" href="plfa.part2.Lambda.html#20304" class="InductiveConstructor">ξ-·₂</a> <a id="29098" href="plfa.part2.Lambda.html#12193" class="InductiveConstructor">V-ƛ</a> <a id="29102" class="Symbol">(</a><a id="29103" href="plfa.part2.Lambda.html#20399" class="InductiveConstructor">β-ƛ</a> <a id="29107" href="plfa.part2.Lambda.html#12254" class="InductiveConstructor">V-zero</a><a id="29113" class="Symbol">))</a> <a id="29116" href="plfa.part2.Lambda.html#23253" class="InductiveConstructor Operator">⟩</a>
    <a id="29122" class="Symbol">(</a><a id="29123" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3854" class="InductiveConstructor Operator">ƛ</a> <a id="29125" class="String">&quot;z&quot;</a> <a id="29129" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a> <a id="29131" href="plfa.part2.Lambda.html#5938" class="Function">sucᶜ</a> <a id="29136" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="29138" class="Symbol">(</a><a id="29139" href="plfa.part2.Lambda.html#5938" class="Function">sucᶜ</a> <a id="29144" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="29146" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="29148" class="String">&quot;z&quot;</a><a id="29151" class="Symbol">))</a> <a id="29154" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="29156" class="Symbol">(</a><a id="29157" href="plfa.part2.Lambda.html#5938" class="Function">sucᶜ</a> <a id="29162" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="29164" class="Symbol">(</a><a id="29165" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="29170" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a><a id="29175" class="Symbol">))</a>
  <a id="29180" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23253" class="InductiveConstructor Operator">—→⟨</a> <a id="29184" href="plfa.part2.Lambda.html#20304" class="InductiveConstructor">ξ-·₂</a> <a id="29189" href="plfa.part2.Lambda.html#12193" class="InductiveConstructor">V-ƛ</a> <a id="29193" class="Symbol">(</a><a id="29194" href="plfa.part2.Lambda.html#20399" class="InductiveConstructor">β-ƛ</a> <a id="29198" class="Symbol">(</a><a id="29199" href="plfa.part2.Lambda.html#12302" class="InductiveConstructor">V-suc</a> <a id="29205" href="plfa.part2.Lambda.html#12254" class="InductiveConstructor">V-zero</a><a id="29211" class="Symbol">))</a> <a id="29214" href="plfa.part2.Lambda.html#23253" class="InductiveConstructor Operator">⟩</a>
    <a id="29220" class="Symbol">(</a><a id="29221" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3854" class="InductiveConstructor Operator">ƛ</a> <a id="29223" class="String">&quot;z&quot;</a> <a id="29227" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a> <a id="29229" href="plfa.part2.Lambda.html#5938" class="Function">sucᶜ</a> <a id="29234" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="29236" class="Symbol">(</a><a id="29237" href="plfa.part2.Lambda.html#5938" class="Function">sucᶜ</a> <a id="29242" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="29244" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="29246" class="String">&quot;z&quot;</a><a id="29249" class="Symbol">))</a> <a id="29252" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="29254" class="Symbol">(</a><a id="29255" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="29260" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="29265" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a><a id="29270" class="Symbol">)</a>
  <a id="29274" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23253" class="InductiveConstructor Operator">—→⟨</a> <a id="29278" href="plfa.part2.Lambda.html#20399" class="InductiveConstructor">β-ƛ</a> <a id="29282" class="Symbol">(</a><a id="29283" href="plfa.part2.Lambda.html#12302" class="InductiveConstructor">V-suc</a> <a id="29289" class="Symbol">(</a><a id="29290" href="plfa.part2.Lambda.html#12302" class="InductiveConstructor">V-suc</a> <a id="29296" href="plfa.part2.Lambda.html#12254" class="InductiveConstructor">V-zero</a><a id="29302" class="Symbol">))</a> <a id="29305" href="plfa.part2.Lambda.html#23253" class="InductiveConstructor Operator">⟩</a>
    <a id="29311" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#5938" class="Function">sucᶜ</a> <a id="29316" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="29318" class="Symbol">(</a><a id="29319" href="plfa.part2.Lambda.html#5938" class="Function">sucᶜ</a> <a id="29324" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="29326" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="29331" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="29336" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a><a id="29341" class="Symbol">)</a>
  <a id="29345" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23253" class="InductiveConstructor Operator">—→⟨</a> <a id="29349" href="plfa.part2.Lambda.html#20304" class="InductiveConstructor">ξ-·₂</a> <a id="29354" href="plfa.part2.Lambda.html#12193" class="InductiveConstructor">V-ƛ</a> <a id="29358" class="Symbol">(</a><a id="29359" href="plfa.part2.Lambda.html#20399" class="InductiveConstructor">β-ƛ</a> <a id="29363" class="Symbol">(</a><a id="29364" href="plfa.part2.Lambda.html#12302" class="InductiveConstructor">V-suc</a> <a id="29370" class="Symbol">(</a><a id="29371" href="plfa.part2.Lambda.html#12302" class="InductiveConstructor">V-suc</a> <a id="29377" href="plfa.part2.Lambda.html#12254" class="InductiveConstructor">V-zero</a><a id="29383" class="Symbol">)))</a> <a id="29387" href="plfa.part2.Lambda.html#23253" class="InductiveConstructor Operator">⟩</a>
    <a id="29393" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#5938" class="Function">sucᶜ</a> <a id="29398" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="29400" class="Symbol">(</a><a id="29401" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="29406" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="29411" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="29416" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a><a id="29421" class="Symbol">)</a>
  <a id="29425" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23253" class="InductiveConstructor Operator">—→⟨</a> <a id="29429" href="plfa.part2.Lambda.html#20399" class="InductiveConstructor">β-ƛ</a> <a id="29433" class="Symbol">(</a><a id="29434" href="plfa.part2.Lambda.html#12302" class="InductiveConstructor">V-suc</a> <a id="29440" class="Symbol">(</a><a id="29441" href="plfa.part2.Lambda.html#12302" class="InductiveConstructor">V-suc</a> <a id="29447" class="Symbol">(</a><a id="29448" href="plfa.part2.Lambda.html#12302" class="InductiveConstructor">V-suc</a> <a id="29454" href="plfa.part2.Lambda.html#12254" class="InductiveConstructor">V-zero</a><a id="29460" class="Symbol">)))</a> <a id="29464" href="plfa.part2.Lambda.html#23253" class="InductiveConstructor Operator">⟩</a>
   <a id="29469" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3982" class="InductiveConstructor Operator">`suc</a> <a id="29474" class="Symbol">(</a><a id="29475" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="29480" class="Symbol">(</a><a id="29481" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="29486" class="Symbol">(</a><a id="29487" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="29492" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a><a id="29497" class="Symbol">)))</a>
  <a id="29503" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23212" class="InductiveConstructor Operator">∎</a>
</pre>{% endraw %}
In the next chapter, we will see how to compute such reduction sequences.


#### Exercise `plus-example` (practice)

Write out the reduction sequence demonstrating that one plus one is two.

{% raw %}<pre class="Agda"><a id="29705" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}

## Syntax of types

We have just two types:

  * Functions, `A ⇒ B`
  * Naturals, `` `ℕ ``

As before, to avoid overlap we use variants of the names used by Agda.

Here is the syntax of types in BNF:

    A, B, C  ::=  A ⇒ B | `ℕ

And here it is formalised in Agda:

{% raw %}<pre class="Agda"><a id="30005" class="Keyword">infixr</a> <a id="30012" class="Number">7</a> <a id="30014" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#30043" class="InductiveConstructor Operator">_⇒_</a>

<a id="30019" class="Keyword">data</a> <a id="Type"></a><a id="30024" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#30024" class="Datatype">Type</a> <a id="30029" class="Symbol">:</a> <a id="30031" class="PrimitiveType">Set</a> <a id="30035" class="Keyword">where</a>
  <a id="Type._⇒_"></a><a id="30043" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#30043" class="InductiveConstructor Operator">_⇒_</a> <a id="30047" class="Symbol">:</a> <a id="30049" href="plfa.part2.Lambda.html#30024" class="Datatype">Type</a> <a id="30054" class="Symbol">→</a> <a id="30056" href="plfa.part2.Lambda.html#30024" class="Datatype">Type</a> <a id="30061" class="Symbol">→</a> <a id="30063" href="plfa.part2.Lambda.html#30024" class="Datatype">Type</a>
  <a id="Type.`ℕ"></a><a id="30070" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#30070" class="InductiveConstructor">`ℕ</a> <a id="30073" class="Symbol">:</a> <a id="30075" href="plfa.part2.Lambda.html#30024" class="Datatype">Type</a>
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

{% raw %}<pre class="Agda"><a id="31660" class="Keyword">infixl</a> <a id="31667" class="Number">5</a>  <a id="31670" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#31722" class="InductiveConstructor Operator">_,_⦂_</a>

<a id="31677" class="Keyword">data</a> <a id="Context"></a><a id="31682" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#31682" class="Datatype">Context</a> <a id="31690" class="Symbol">:</a> <a id="31692" class="PrimitiveType">Set</a> <a id="31696" class="Keyword">where</a>
  <a id="Context.∅"></a><a id="31704" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#31704" class="InductiveConstructor">∅</a>     <a id="31710" class="Symbol">:</a> <a id="31712" href="plfa.part2.Lambda.html#31682" class="Datatype">Context</a>
  <a id="Context._,_⦂_"></a><a id="31722" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#31722" class="InductiveConstructor Operator">_,_⦂_</a> <a id="31728" class="Symbol">:</a> <a id="31730" href="plfa.part2.Lambda.html#31682" class="Datatype">Context</a> <a id="31738" class="Symbol">→</a> <a id="31740" href="plfa.part2.Lambda.html#3695" class="Function">Id</a> <a id="31743" class="Symbol">→</a> <a id="31745" href="plfa.part2.Lambda.html#30024" class="Datatype">Type</a> <a id="31750" class="Symbol">→</a> <a id="31752" href="plfa.part2.Lambda.html#31682" class="Datatype">Context</a>
</pre>{% endraw %}

#### Exercise `Context-≃` (practice)

Show that `Context` is isomorphic to `List (Id × Type)`.
For instance, the isomorphism relates the context

    ∅ , "s" ⦂ `ℕ ⇒ `ℕ , "z" ⦂ `ℕ

to the list

    [ ⟨ "z" , `ℕ ⟩ , ⟨ "s" , `ℕ ⇒ `ℕ ⟩ ]

{% raw %}<pre class="Agda"><a id="32005" class="Comment">-- Your code goes here</a>
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
{% raw %}<pre class="Agda"><a id="32894" class="Keyword">infix</a>  <a id="32901" class="Number">4</a>  <a id="32904" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#32916" class="Datatype Operator">_∋_⦂_</a>

<a id="32911" class="Keyword">data</a> <a id="_∋_⦂_"></a><a id="32916" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#32916" class="Datatype Operator">_∋_⦂_</a> <a id="32922" class="Symbol">:</a> <a id="32924" href="plfa.part2.Lambda.html#31682" class="Datatype">Context</a> <a id="32932" class="Symbol">→</a> <a id="32934" href="plfa.part2.Lambda.html#3695" class="Function">Id</a> <a id="32937" class="Symbol">→</a> <a id="32939" href="plfa.part2.Lambda.html#30024" class="Datatype">Type</a> <a id="32944" class="Symbol">→</a> <a id="32946" class="PrimitiveType">Set</a> <a id="32950" class="Keyword">where</a>

  <a id="_∋_⦂_.Z"></a><a id="32959" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#32959" class="InductiveConstructor">Z</a> <a id="32961" class="Symbol">:</a> <a id="32963" class="Symbol">∀</a> <a id="32965" class="Symbol">{</a><a id="32966" href="plfa.part2.Lambda.html#32966" class="Bound">Γ</a> <a id="32968" href="plfa.part2.Lambda.html#32968" class="Bound">x</a> <a id="32970" href="plfa.part2.Lambda.html#32970" class="Bound">A</a><a id="32971" class="Symbol">}</a>
      <a id="32979" class="Comment">------------------</a>
    <a id="33002" class="Symbol">→</a> <a id="33004" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#32966" class="Bound">Γ</a> <a id="33006" href="plfa.part2.Lambda.html#31722" class="InductiveConstructor Operator">,</a> <a id="33008" href="plfa.part2.Lambda.html#32968" class="Bound">x</a> <a id="33010" href="plfa.part2.Lambda.html#31722" class="InductiveConstructor Operator">⦂</a> <a id="33012" href="plfa.part2.Lambda.html#32970" class="Bound">A</a> <a id="33014" href="plfa.part2.Lambda.html#32916" class="Datatype Operator">∋</a> <a id="33016" href="plfa.part2.Lambda.html#32968" class="Bound">x</a> <a id="33018" href="plfa.part2.Lambda.html#32916" class="Datatype Operator">⦂</a> <a id="33020" href="plfa.part2.Lambda.html#32970" class="Bound">A</a>

  <a id="_∋_⦂_.S"></a><a id="33025" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#33025" class="InductiveConstructor">S</a> <a id="33027" class="Symbol">:</a> <a id="33029" class="Symbol">∀</a> <a id="33031" class="Symbol">{</a><a id="33032" href="plfa.part2.Lambda.html#33032" class="Bound">Γ</a> <a id="33034" href="plfa.part2.Lambda.html#33034" class="Bound">x</a> <a id="33036" href="plfa.part2.Lambda.html#33036" class="Bound">y</a> <a id="33038" href="plfa.part2.Lambda.html#33038" class="Bound">A</a> <a id="33040" href="plfa.part2.Lambda.html#33040" class="Bound">B</a><a id="33041" class="Symbol">}</a>
    <a id="33047" class="Symbol">→</a> <a id="33049" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#33034" class="Bound">x</a> <a id="33051" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#799" class="Function Operator">≢</a> <a id="33053" href="plfa.part2.Lambda.html#33036" class="Bound">y</a>
    <a id="33059" class="Symbol">→</a> <a id="33061" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#33032" class="Bound">Γ</a> <a id="33063" href="plfa.part2.Lambda.html#32916" class="Datatype Operator">∋</a> <a id="33065" href="plfa.part2.Lambda.html#33034" class="Bound">x</a> <a id="33067" href="plfa.part2.Lambda.html#32916" class="Datatype Operator">⦂</a> <a id="33069" href="plfa.part2.Lambda.html#33038" class="Bound">A</a>
      <a id="33077" class="Comment">------------------</a>
    <a id="33100" class="Symbol">→</a> <a id="33102" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#33032" class="Bound">Γ</a> <a id="33104" href="plfa.part2.Lambda.html#31722" class="InductiveConstructor Operator">,</a> <a id="33106" href="plfa.part2.Lambda.html#33036" class="Bound">y</a> <a id="33108" href="plfa.part2.Lambda.html#31722" class="InductiveConstructor Operator">⦂</a> <a id="33110" href="plfa.part2.Lambda.html#33040" class="Bound">B</a> <a id="33112" href="plfa.part2.Lambda.html#32916" class="Datatype Operator">∋</a> <a id="33114" href="plfa.part2.Lambda.html#33034" class="Bound">x</a> <a id="33116" href="plfa.part2.Lambda.html#32916" class="Datatype Operator">⦂</a> <a id="33118" href="plfa.part2.Lambda.html#33038" class="Bound">A</a>
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
{% raw %}<pre class="Agda"><a id="34058" class="Keyword">infix</a>  <a id="34065" class="Number">4</a>  <a id="34068" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#34080" class="Datatype Operator">_⊢_⦂_</a>

<a id="34075" class="Keyword">data</a> <a id="_⊢_⦂_"></a><a id="34080" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#34080" class="Datatype Operator">_⊢_⦂_</a> <a id="34086" class="Symbol">:</a> <a id="34088" href="plfa.part2.Lambda.html#31682" class="Datatype">Context</a> <a id="34096" class="Symbol">→</a> <a id="34098" href="plfa.part2.Lambda.html#3796" class="Datatype">Term</a> <a id="34103" class="Symbol">→</a> <a id="34105" href="plfa.part2.Lambda.html#30024" class="Datatype">Type</a> <a id="34110" class="Symbol">→</a> <a id="34112" class="PrimitiveType">Set</a> <a id="34116" class="Keyword">where</a>

  <a id="34125" class="Comment">-- Axiom</a>
  <a id="_⊢_⦂_.⊢`"></a><a id="34136" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#34136" class="InductiveConstructor">⊢`</a> <a id="34139" class="Symbol">:</a> <a id="34141" class="Symbol">∀</a> <a id="34143" class="Symbol">{</a><a id="34144" href="plfa.part2.Lambda.html#34144" class="Bound">Γ</a> <a id="34146" href="plfa.part2.Lambda.html#34146" class="Bound">x</a> <a id="34148" href="plfa.part2.Lambda.html#34148" class="Bound">A</a><a id="34149" class="Symbol">}</a>
    <a id="34155" class="Symbol">→</a> <a id="34157" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#34144" class="Bound">Γ</a> <a id="34159" href="plfa.part2.Lambda.html#32916" class="Datatype Operator">∋</a> <a id="34161" href="plfa.part2.Lambda.html#34146" class="Bound">x</a> <a id="34163" href="plfa.part2.Lambda.html#32916" class="Datatype Operator">⦂</a> <a id="34165" href="plfa.part2.Lambda.html#34148" class="Bound">A</a>
      <a id="34173" class="Comment">-----------</a>
    <a id="34189" class="Symbol">→</a> <a id="34191" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#34144" class="Bound">Γ</a> <a id="34193" href="plfa.part2.Lambda.html#34080" class="Datatype Operator">⊢</a> <a id="34195" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="34197" href="plfa.part2.Lambda.html#34146" class="Bound">x</a> <a id="34199" href="plfa.part2.Lambda.html#34080" class="Datatype Operator">⦂</a> <a id="34201" href="plfa.part2.Lambda.html#34148" class="Bound">A</a>

  <a id="34206" class="Comment">-- ⇒-I</a>
  <a id="_⊢_⦂_.⊢ƛ"></a><a id="34215" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#34215" class="InductiveConstructor">⊢ƛ</a> <a id="34218" class="Symbol">:</a> <a id="34220" class="Symbol">∀</a> <a id="34222" class="Symbol">{</a><a id="34223" href="plfa.part2.Lambda.html#34223" class="Bound">Γ</a> <a id="34225" href="plfa.part2.Lambda.html#34225" class="Bound">x</a> <a id="34227" href="plfa.part2.Lambda.html#34227" class="Bound">N</a> <a id="34229" href="plfa.part2.Lambda.html#34229" class="Bound">A</a> <a id="34231" href="plfa.part2.Lambda.html#34231" class="Bound">B</a><a id="34232" class="Symbol">}</a>
    <a id="34238" class="Symbol">→</a> <a id="34240" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#34223" class="Bound">Γ</a> <a id="34242" href="plfa.part2.Lambda.html#31722" class="InductiveConstructor Operator">,</a> <a id="34244" href="plfa.part2.Lambda.html#34225" class="Bound">x</a> <a id="34246" href="plfa.part2.Lambda.html#31722" class="InductiveConstructor Operator">⦂</a> <a id="34248" href="plfa.part2.Lambda.html#34229" class="Bound">A</a> <a id="34250" href="plfa.part2.Lambda.html#34080" class="Datatype Operator">⊢</a> <a id="34252" href="plfa.part2.Lambda.html#34227" class="Bound">N</a> <a id="34254" href="plfa.part2.Lambda.html#34080" class="Datatype Operator">⦂</a> <a id="34256" href="plfa.part2.Lambda.html#34231" class="Bound">B</a>
      <a id="34264" class="Comment">-------------------</a>
    <a id="34288" class="Symbol">→</a> <a id="34290" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#34223" class="Bound">Γ</a> <a id="34292" href="plfa.part2.Lambda.html#34080" class="Datatype Operator">⊢</a> <a id="34294" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">ƛ</a> <a id="34296" href="plfa.part2.Lambda.html#34225" class="Bound">x</a> <a id="34298" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a> <a id="34300" href="plfa.part2.Lambda.html#34227" class="Bound">N</a> <a id="34302" href="plfa.part2.Lambda.html#34080" class="Datatype Operator">⦂</a> <a id="34304" href="plfa.part2.Lambda.html#34229" class="Bound">A</a> <a id="34306" href="plfa.part2.Lambda.html#30043" class="InductiveConstructor Operator">⇒</a> <a id="34308" href="plfa.part2.Lambda.html#34231" class="Bound">B</a>

  <a id="34313" class="Comment">-- ⇒-E</a>
  <a id="_⊢_⦂_._·_"></a><a id="34322" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#34322" class="InductiveConstructor Operator">_·_</a> <a id="34326" class="Symbol">:</a> <a id="34328" class="Symbol">∀</a> <a id="34330" class="Symbol">{</a><a id="34331" href="plfa.part2.Lambda.html#34331" class="Bound">Γ</a> <a id="34333" href="plfa.part2.Lambda.html#34333" class="Bound">L</a> <a id="34335" href="plfa.part2.Lambda.html#34335" class="Bound">M</a> <a id="34337" href="plfa.part2.Lambda.html#34337" class="Bound">A</a> <a id="34339" href="plfa.part2.Lambda.html#34339" class="Bound">B</a><a id="34340" class="Symbol">}</a>
    <a id="34346" class="Symbol">→</a> <a id="34348" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#34331" class="Bound">Γ</a> <a id="34350" href="plfa.part2.Lambda.html#34080" class="Datatype Operator">⊢</a> <a id="34352" href="plfa.part2.Lambda.html#34333" class="Bound">L</a> <a id="34354" href="plfa.part2.Lambda.html#34080" class="Datatype Operator">⦂</a> <a id="34356" href="plfa.part2.Lambda.html#34337" class="Bound">A</a> <a id="34358" href="plfa.part2.Lambda.html#30043" class="InductiveConstructor Operator">⇒</a> <a id="34360" href="plfa.part2.Lambda.html#34339" class="Bound">B</a>
    <a id="34366" class="Symbol">→</a> <a id="34368" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#34331" class="Bound">Γ</a> <a id="34370" href="plfa.part2.Lambda.html#34080" class="Datatype Operator">⊢</a> <a id="34372" href="plfa.part2.Lambda.html#34335" class="Bound">M</a> <a id="34374" href="plfa.part2.Lambda.html#34080" class="Datatype Operator">⦂</a> <a id="34376" href="plfa.part2.Lambda.html#34337" class="Bound">A</a>
      <a id="34384" class="Comment">-------------</a>
    <a id="34402" class="Symbol">→</a> <a id="34404" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#34331" class="Bound">Γ</a> <a id="34406" href="plfa.part2.Lambda.html#34080" class="Datatype Operator">⊢</a> <a id="34408" href="plfa.part2.Lambda.html#34333" class="Bound">L</a> <a id="34410" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="34412" href="plfa.part2.Lambda.html#34335" class="Bound">M</a> <a id="34414" href="plfa.part2.Lambda.html#34080" class="Datatype Operator">⦂</a> <a id="34416" href="plfa.part2.Lambda.html#34339" class="Bound">B</a>

  <a id="34421" class="Comment">-- ℕ-I₁</a>
  <a id="_⊢_⦂_.⊢zero"></a><a id="34431" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#34431" class="InductiveConstructor">⊢zero</a> <a id="34437" class="Symbol">:</a> <a id="34439" class="Symbol">∀</a> <a id="34441" class="Symbol">{</a><a id="34442" href="plfa.part2.Lambda.html#34442" class="Bound">Γ</a><a id="34443" class="Symbol">}</a>
      <a id="34451" class="Comment">--------------</a>
    <a id="34470" class="Symbol">→</a> <a id="34472" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#34442" class="Bound">Γ</a> <a id="34474" href="plfa.part2.Lambda.html#34080" class="Datatype Operator">⊢</a> <a id="34476" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a> <a id="34482" href="plfa.part2.Lambda.html#34080" class="Datatype Operator">⦂</a> <a id="34484" href="plfa.part2.Lambda.html#30070" class="InductiveConstructor">`ℕ</a>

  <a id="34490" class="Comment">-- ℕ-I₂</a>
  <a id="_⊢_⦂_.⊢suc"></a><a id="34500" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#34500" class="InductiveConstructor">⊢suc</a> <a id="34505" class="Symbol">:</a> <a id="34507" class="Symbol">∀</a> <a id="34509" class="Symbol">{</a><a id="34510" href="plfa.part2.Lambda.html#34510" class="Bound">Γ</a> <a id="34512" href="plfa.part2.Lambda.html#34512" class="Bound">M</a><a id="34513" class="Symbol">}</a>
    <a id="34519" class="Symbol">→</a> <a id="34521" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#34510" class="Bound">Γ</a> <a id="34523" href="plfa.part2.Lambda.html#34080" class="Datatype Operator">⊢</a> <a id="34525" href="plfa.part2.Lambda.html#34512" class="Bound">M</a> <a id="34527" href="plfa.part2.Lambda.html#34080" class="Datatype Operator">⦂</a> <a id="34529" href="plfa.part2.Lambda.html#30070" class="InductiveConstructor">`ℕ</a>
      <a id="34538" class="Comment">---------------</a>
    <a id="34558" class="Symbol">→</a> <a id="34560" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#34510" class="Bound">Γ</a> <a id="34562" href="plfa.part2.Lambda.html#34080" class="Datatype Operator">⊢</a> <a id="34564" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="34569" href="plfa.part2.Lambda.html#34512" class="Bound">M</a> <a id="34571" href="plfa.part2.Lambda.html#34080" class="Datatype Operator">⦂</a> <a id="34573" href="plfa.part2.Lambda.html#30070" class="InductiveConstructor">`ℕ</a>

  <a id="34579" class="Comment">-- ℕ-E</a>
  <a id="_⊢_⦂_.⊢case"></a><a id="34588" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#34588" class="InductiveConstructor">⊢case</a> <a id="34594" class="Symbol">:</a> <a id="34596" class="Symbol">∀</a> <a id="34598" class="Symbol">{</a><a id="34599" href="plfa.part2.Lambda.html#34599" class="Bound">Γ</a> <a id="34601" href="plfa.part2.Lambda.html#34601" class="Bound">L</a> <a id="34603" href="plfa.part2.Lambda.html#34603" class="Bound">M</a> <a id="34605" href="plfa.part2.Lambda.html#34605" class="Bound">x</a> <a id="34607" href="plfa.part2.Lambda.html#34607" class="Bound">N</a> <a id="34609" href="plfa.part2.Lambda.html#34609" class="Bound">A</a><a id="34610" class="Symbol">}</a>
    <a id="34616" class="Symbol">→</a> <a id="34618" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#34599" class="Bound">Γ</a> <a id="34620" href="plfa.part2.Lambda.html#34080" class="Datatype Operator">⊢</a> <a id="34622" href="plfa.part2.Lambda.html#34601" class="Bound">L</a> <a id="34624" href="plfa.part2.Lambda.html#34080" class="Datatype Operator">⦂</a> <a id="34626" href="plfa.part2.Lambda.html#30070" class="InductiveConstructor">`ℕ</a>
    <a id="34633" class="Symbol">→</a> <a id="34635" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#34599" class="Bound">Γ</a> <a id="34637" href="plfa.part2.Lambda.html#34080" class="Datatype Operator">⊢</a> <a id="34639" href="plfa.part2.Lambda.html#34603" class="Bound">M</a> <a id="34641" href="plfa.part2.Lambda.html#34080" class="Datatype Operator">⦂</a> <a id="34643" href="plfa.part2.Lambda.html#34609" class="Bound">A</a>
    <a id="34649" class="Symbol">→</a> <a id="34651" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#34599" class="Bound">Γ</a> <a id="34653" href="plfa.part2.Lambda.html#31722" class="InductiveConstructor Operator">,</a> <a id="34655" href="plfa.part2.Lambda.html#34605" class="Bound">x</a> <a id="34657" href="plfa.part2.Lambda.html#31722" class="InductiveConstructor Operator">⦂</a> <a id="34659" href="plfa.part2.Lambda.html#30070" class="InductiveConstructor">`ℕ</a> <a id="34662" href="plfa.part2.Lambda.html#34080" class="Datatype Operator">⊢</a> <a id="34664" href="plfa.part2.Lambda.html#34607" class="Bound">N</a> <a id="34666" href="plfa.part2.Lambda.html#34080" class="Datatype Operator">⦂</a> <a id="34668" href="plfa.part2.Lambda.html#34609" class="Bound">A</a>
      <a id="34676" class="Comment">-------------------------------------</a>
    <a id="34718" class="Symbol">→</a> <a id="34720" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#34599" class="Bound">Γ</a> <a id="34722" href="plfa.part2.Lambda.html#34080" class="Datatype Operator">⊢</a> <a id="34724" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">case</a> <a id="34729" href="plfa.part2.Lambda.html#34601" class="Bound">L</a> <a id="34731" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">[zero⇒</a> <a id="34738" href="plfa.part2.Lambda.html#34603" class="Bound">M</a> <a id="34740" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">|suc</a> <a id="34745" href="plfa.part2.Lambda.html#34605" class="Bound">x</a> <a id="34747" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">⇒</a> <a id="34749" href="plfa.part2.Lambda.html#34607" class="Bound">N</a> <a id="34751" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">]</a> <a id="34753" href="plfa.part2.Lambda.html#34080" class="Datatype Operator">⦂</a> <a id="34755" href="plfa.part2.Lambda.html#34609" class="Bound">A</a>

  <a id="_⊢_⦂_.⊢μ"></a><a id="34760" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#34760" class="InductiveConstructor">⊢μ</a> <a id="34763" class="Symbol">:</a> <a id="34765" class="Symbol">∀</a> <a id="34767" class="Symbol">{</a><a id="34768" href="plfa.part2.Lambda.html#34768" class="Bound">Γ</a> <a id="34770" href="plfa.part2.Lambda.html#34770" class="Bound">x</a> <a id="34772" href="plfa.part2.Lambda.html#34772" class="Bound">M</a> <a id="34774" href="plfa.part2.Lambda.html#34774" class="Bound">A</a><a id="34775" class="Symbol">}</a>
    <a id="34781" class="Symbol">→</a> <a id="34783" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#34768" class="Bound">Γ</a> <a id="34785" href="plfa.part2.Lambda.html#31722" class="InductiveConstructor Operator">,</a> <a id="34787" href="plfa.part2.Lambda.html#34770" class="Bound">x</a> <a id="34789" href="plfa.part2.Lambda.html#31722" class="InductiveConstructor Operator">⦂</a> <a id="34791" href="plfa.part2.Lambda.html#34774" class="Bound">A</a> <a id="34793" href="plfa.part2.Lambda.html#34080" class="Datatype Operator">⊢</a> <a id="34795" href="plfa.part2.Lambda.html#34772" class="Bound">M</a> <a id="34797" href="plfa.part2.Lambda.html#34080" class="Datatype Operator">⦂</a> <a id="34799" href="plfa.part2.Lambda.html#34774" class="Bound">A</a>
      <a id="34807" class="Comment">-----------------</a>
    <a id="34829" class="Symbol">→</a> <a id="34831" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#34768" class="Bound">Γ</a> <a id="34833" href="plfa.part2.Lambda.html#34080" class="Datatype Operator">⊢</a> <a id="34835" href="plfa.part2.Lambda.html#4083" class="InductiveConstructor Operator">μ</a> <a id="34837" href="plfa.part2.Lambda.html#34770" class="Bound">x</a> <a id="34839" href="plfa.part2.Lambda.html#4083" class="InductiveConstructor Operator">⇒</a> <a id="34841" href="plfa.part2.Lambda.html#34772" class="Bound">M</a> <a id="34843" href="plfa.part2.Lambda.html#34080" class="Datatype Operator">⦂</a> <a id="34845" href="plfa.part2.Lambda.html#34774" class="Bound">A</a>
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
{% raw %}<pre class="Agda"><a id="Ch"></a><a id="37329" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#37329" class="Function">Ch</a> <a id="37332" class="Symbol">:</a> <a id="37334" href="plfa.part2.Lambda.html#30024" class="Datatype">Type</a> <a id="37339" class="Symbol">→</a> <a id="37341" href="plfa.part2.Lambda.html#30024" class="Datatype">Type</a>
<a id="37346" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#37329" class="Function">Ch</a> <a id="37349" href="plfa.part2.Lambda.html#37349" class="Bound">A</a> <a id="37351" class="Symbol">=</a> <a id="37353" class="Symbol">(</a><a id="37354" href="plfa.part2.Lambda.html#37349" class="Bound">A</a> <a id="37356" href="plfa.part2.Lambda.html#30043" class="InductiveConstructor Operator">⇒</a> <a id="37358" href="plfa.part2.Lambda.html#37349" class="Bound">A</a><a id="37359" class="Symbol">)</a> <a id="37361" href="plfa.part2.Lambda.html#30043" class="InductiveConstructor Operator">⇒</a> <a id="37363" href="plfa.part2.Lambda.html#37349" class="Bound">A</a> <a id="37365" href="plfa.part2.Lambda.html#30043" class="InductiveConstructor Operator">⇒</a> <a id="37367" href="plfa.part2.Lambda.html#37349" class="Bound">A</a>

<a id="⊢twoᶜ"></a><a id="37370" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#37370" class="Function">⊢twoᶜ</a> <a id="37376" class="Symbol">:</a> <a id="37378" class="Symbol">∀</a> <a id="37380" class="Symbol">{</a><a id="37381" href="plfa.part2.Lambda.html#37381" class="Bound">Γ</a> <a id="37383" href="plfa.part2.Lambda.html#37383" class="Bound">A</a><a id="37384" class="Symbol">}</a> <a id="37386" class="Symbol">→</a> <a id="37388" href="plfa.part2.Lambda.html#37381" class="Bound">Γ</a> <a id="37390" href="plfa.part2.Lambda.html#34080" class="Datatype Operator">⊢</a> <a id="37392" href="plfa.part2.Lambda.html#5773" class="Function">twoᶜ</a> <a id="37397" href="plfa.part2.Lambda.html#34080" class="Datatype Operator">⦂</a> <a id="37399" href="plfa.part2.Lambda.html#37329" class="Function">Ch</a> <a id="37402" href="plfa.part2.Lambda.html#37383" class="Bound">A</a>
<a id="37404" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#37370" class="Function">⊢twoᶜ</a> <a id="37410" class="Symbol">=</a> <a id="37412" href="plfa.part2.Lambda.html#34215" class="InductiveConstructor">⊢ƛ</a> <a id="37415" class="Symbol">(</a><a id="37416" href="plfa.part2.Lambda.html#34215" class="InductiveConstructor">⊢ƛ</a> <a id="37419" class="Symbol">(</a><a id="37420" href="plfa.part2.Lambda.html#34136" class="InductiveConstructor">⊢`</a> <a id="37423" href="plfa.part2.Lambda.html#37456" class="Function">∋s</a> <a id="37426" href="plfa.part2.Lambda.html#34322" class="InductiveConstructor Operator">·</a> <a id="37428" class="Symbol">(</a><a id="37429" href="plfa.part2.Lambda.html#34136" class="InductiveConstructor">⊢`</a> <a id="37432" href="plfa.part2.Lambda.html#37456" class="Function">∋s</a> <a id="37435" href="plfa.part2.Lambda.html#34322" class="InductiveConstructor Operator">·</a> <a id="37437" href="plfa.part2.Lambda.html#34136" class="InductiveConstructor">⊢`</a> <a id="37440" href="plfa.part2.Lambda.html#37473" class="Function">∋z</a><a id="37442" class="Symbol">)))</a>
  <a id="37448" class="Keyword">where</a>
  <a id="37456" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#37456" class="Function">∋s</a> <a id="37459" class="Symbol">=</a> <a id="37461" href="plfa.part2.Lambda.html#33025" class="InductiveConstructor">S</a> <a id="37463" class="Symbol">(λ())</a> <a id="37469" href="plfa.part2.Lambda.html#32959" class="InductiveConstructor">Z</a>
  <a id="37473" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#37473" class="Function">∋z</a> <a id="37476" class="Symbol">=</a> <a id="37478" href="plfa.part2.Lambda.html#32959" class="InductiveConstructor">Z</a>
</pre>{% endraw %}
Here are the typings corresponding to computing two plus two:
{% raw %}<pre class="Agda"><a id="⊢two"></a><a id="37551" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#37551" class="Function">⊢two</a> <a id="37556" class="Symbol">:</a> <a id="37558" class="Symbol">∀</a> <a id="37560" class="Symbol">{</a><a id="37561" href="plfa.part2.Lambda.html#37561" class="Bound">Γ</a><a id="37562" class="Symbol">}</a> <a id="37564" class="Symbol">→</a> <a id="37566" href="plfa.part2.Lambda.html#37561" class="Bound">Γ</a> <a id="37568" href="plfa.part2.Lambda.html#34080" class="Datatype Operator">⊢</a> <a id="37570" href="plfa.part2.Lambda.html#4524" class="Function">two</a> <a id="37574" href="plfa.part2.Lambda.html#34080" class="Datatype Operator">⦂</a> <a id="37576" href="plfa.part2.Lambda.html#30070" class="InductiveConstructor">`ℕ</a>
<a id="37579" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#37551" class="Function">⊢two</a> <a id="37584" class="Symbol">=</a> <a id="37586" href="plfa.part2.Lambda.html#34500" class="InductiveConstructor">⊢suc</a> <a id="37591" class="Symbol">(</a><a id="37592" href="plfa.part2.Lambda.html#34500" class="InductiveConstructor">⊢suc</a> <a id="37597" href="plfa.part2.Lambda.html#34431" class="InductiveConstructor">⊢zero</a><a id="37602" class="Symbol">)</a>

<a id="⊢plus"></a><a id="37605" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#37605" class="Function">⊢plus</a> <a id="37611" class="Symbol">:</a> <a id="37613" class="Symbol">∀</a> <a id="37615" class="Symbol">{</a><a id="37616" href="plfa.part2.Lambda.html#37616" class="Bound">Γ</a><a id="37617" class="Symbol">}</a> <a id="37619" class="Symbol">→</a> <a id="37621" href="plfa.part2.Lambda.html#37616" class="Bound">Γ</a> <a id="37623" href="plfa.part2.Lambda.html#34080" class="Datatype Operator">⊢</a> <a id="37625" href="plfa.part2.Lambda.html#4558" class="Function">plus</a> <a id="37630" href="plfa.part2.Lambda.html#34080" class="Datatype Operator">⦂</a> <a id="37632" href="plfa.part2.Lambda.html#30070" class="InductiveConstructor">`ℕ</a> <a id="37635" href="plfa.part2.Lambda.html#30043" class="InductiveConstructor Operator">⇒</a> <a id="37637" href="plfa.part2.Lambda.html#30070" class="InductiveConstructor">`ℕ</a> <a id="37640" href="plfa.part2.Lambda.html#30043" class="InductiveConstructor Operator">⇒</a> <a id="37642" href="plfa.part2.Lambda.html#30070" class="InductiveConstructor">`ℕ</a>
<a id="37645" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#37605" class="Function">⊢plus</a> <a id="37651" class="Symbol">=</a> <a id="37653" href="plfa.part2.Lambda.html#34760" class="InductiveConstructor">⊢μ</a> <a id="37656" class="Symbol">(</a><a id="37657" href="plfa.part2.Lambda.html#34215" class="InductiveConstructor">⊢ƛ</a> <a id="37660" class="Symbol">(</a><a id="37661" href="plfa.part2.Lambda.html#34215" class="InductiveConstructor">⊢ƛ</a> <a id="37664" class="Symbol">(</a><a id="37665" href="plfa.part2.Lambda.html#34588" class="InductiveConstructor">⊢case</a> <a id="37671" class="Symbol">(</a><a id="37672" href="plfa.part2.Lambda.html#34136" class="InductiveConstructor">⊢`</a> <a id="37675" href="plfa.part2.Lambda.html#37782" class="Function">∋m</a><a id="37677" class="Symbol">)</a> <a id="37679" class="Symbol">(</a><a id="37680" href="plfa.part2.Lambda.html#34136" class="InductiveConstructor">⊢`</a> <a id="37683" href="plfa.part2.Lambda.html#37802" class="Function">∋n</a><a id="37685" class="Symbol">)</a>
         <a id="37696" class="Symbol">(</a><a id="37697" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#34500" class="InductiveConstructor">⊢suc</a> <a id="37702" class="Symbol">(</a><a id="37703" href="plfa.part2.Lambda.html#34136" class="InductiveConstructor">⊢`</a> <a id="37706" href="plfa.part2.Lambda.html#37742" class="Function">∋+</a> <a id="37709" href="plfa.part2.Lambda.html#34322" class="InductiveConstructor Operator">·</a> <a id="37711" href="plfa.part2.Lambda.html#34136" class="InductiveConstructor">⊢`</a> <a id="37714" href="plfa.part2.Lambda.html#37812" class="Function">∋m′</a> <a id="37718" href="plfa.part2.Lambda.html#34322" class="InductiveConstructor Operator">·</a> <a id="37720" href="plfa.part2.Lambda.html#34136" class="InductiveConstructor">⊢`</a> <a id="37723" href="plfa.part2.Lambda.html#37822" class="Function">∋n′</a><a id="37726" class="Symbol">)))))</a>
  <a id="37734" class="Keyword">where</a>
  <a id="37742" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#37742" class="Function">∋+</a>  <a id="37746" class="Symbol">=</a> <a id="37748" class="Symbol">(</a><a id="37749" href="plfa.part2.Lambda.html#33025" class="InductiveConstructor">S</a> <a id="37751" class="Symbol">(λ())</a> <a id="37757" class="Symbol">(</a><a id="37758" href="plfa.part2.Lambda.html#33025" class="InductiveConstructor">S</a> <a id="37760" class="Symbol">(λ())</a> <a id="37766" class="Symbol">(</a><a id="37767" href="plfa.part2.Lambda.html#33025" class="InductiveConstructor">S</a> <a id="37769" class="Symbol">(λ())</a> <a id="37775" href="plfa.part2.Lambda.html#32959" class="InductiveConstructor">Z</a><a id="37776" class="Symbol">)))</a>
  <a id="37782" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#37782" class="Function">∋m</a>  <a id="37786" class="Symbol">=</a> <a id="37788" class="Symbol">(</a><a id="37789" href="plfa.part2.Lambda.html#33025" class="InductiveConstructor">S</a> <a id="37791" class="Symbol">(λ())</a> <a id="37797" href="plfa.part2.Lambda.html#32959" class="InductiveConstructor">Z</a><a id="37798" class="Symbol">)</a>
  <a id="37802" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#37802" class="Function">∋n</a>  <a id="37806" class="Symbol">=</a> <a id="37808" href="plfa.part2.Lambda.html#32959" class="InductiveConstructor">Z</a>
  <a id="37812" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#37812" class="Function">∋m′</a> <a id="37816" class="Symbol">=</a> <a id="37818" href="plfa.part2.Lambda.html#32959" class="InductiveConstructor">Z</a>
  <a id="37822" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#37822" class="Function">∋n′</a> <a id="37826" class="Symbol">=</a> <a id="37828" class="Symbol">(</a><a id="37829" href="plfa.part2.Lambda.html#33025" class="InductiveConstructor">S</a> <a id="37831" class="Symbol">(λ())</a> <a id="37837" href="plfa.part2.Lambda.html#32959" class="InductiveConstructor">Z</a><a id="37838" class="Symbol">)</a>

<a id="⊢2+2"></a><a id="37841" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#37841" class="Function">⊢2+2</a> <a id="37846" class="Symbol">:</a> <a id="37848" href="plfa.part2.Lambda.html#31704" class="InductiveConstructor">∅</a> <a id="37850" href="plfa.part2.Lambda.html#34080" class="Datatype Operator">⊢</a> <a id="37852" href="plfa.part2.Lambda.html#4558" class="Function">plus</a> <a id="37857" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="37859" href="plfa.part2.Lambda.html#4524" class="Function">two</a> <a id="37863" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="37865" href="plfa.part2.Lambda.html#4524" class="Function">two</a> <a id="37869" href="plfa.part2.Lambda.html#34080" class="Datatype Operator">⦂</a> <a id="37871" href="plfa.part2.Lambda.html#30070" class="InductiveConstructor">`ℕ</a>
<a id="37874" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#37841" class="Function">⊢2+2</a> <a id="37879" class="Symbol">=</a> <a id="37881" href="plfa.part2.Lambda.html#37605" class="Function">⊢plus</a> <a id="37887" href="plfa.part2.Lambda.html#34322" class="InductiveConstructor Operator">·</a> <a id="37889" href="plfa.part2.Lambda.html#37551" class="Function">⊢two</a> <a id="37894" href="plfa.part2.Lambda.html#34322" class="InductiveConstructor Operator">·</a> <a id="37896" href="plfa.part2.Lambda.html#37551" class="Function">⊢two</a>
</pre>{% endraw %}In contrast to our earlier examples, here we have typed `two` and `plus`
in an arbitrary context rather than the empty context; this makes it easy
to use them inside other binding contexts as well as at the top level.
Here the two lookup judgments `∋m` and `∋m′` refer to two different
bindings of variables named `"m"`.  In contrast, the two judgments `∋n` and
`∋n′` both refer to the same binding of `"n"` but accessed in different
contexts, the first where "n" is the last binding in the context, and
the second after "m" is bound in the successor branch of the case.

And here are typings for the remainder of the Church example:
{% raw %}<pre class="Agda"><a id="⊢plusᶜ"></a><a id="38543" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#38543" class="Function">⊢plusᶜ</a> <a id="38550" class="Symbol">:</a> <a id="38552" class="Symbol">∀</a> <a id="38554" class="Symbol">{</a><a id="38555" href="plfa.part2.Lambda.html#38555" class="Bound">Γ</a> <a id="38557" href="plfa.part2.Lambda.html#38557" class="Bound">A</a><a id="38558" class="Symbol">}</a> <a id="38560" class="Symbol">→</a> <a id="38562" href="plfa.part2.Lambda.html#38555" class="Bound">Γ</a>  <a id="38565" href="plfa.part2.Lambda.html#34080" class="Datatype Operator">⊢</a> <a id="38567" href="plfa.part2.Lambda.html#5834" class="Function">plusᶜ</a> <a id="38573" href="plfa.part2.Lambda.html#34080" class="Datatype Operator">⦂</a> <a id="38575" href="plfa.part2.Lambda.html#37329" class="Function">Ch</a> <a id="38578" href="plfa.part2.Lambda.html#38557" class="Bound">A</a> <a id="38580" href="plfa.part2.Lambda.html#30043" class="InductiveConstructor Operator">⇒</a> <a id="38582" href="plfa.part2.Lambda.html#37329" class="Function">Ch</a> <a id="38585" href="plfa.part2.Lambda.html#38557" class="Bound">A</a> <a id="38587" href="plfa.part2.Lambda.html#30043" class="InductiveConstructor Operator">⇒</a> <a id="38589" href="plfa.part2.Lambda.html#37329" class="Function">Ch</a> <a id="38592" href="plfa.part2.Lambda.html#38557" class="Bound">A</a>
<a id="38594" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#38543" class="Function">⊢plusᶜ</a> <a id="38601" class="Symbol">=</a> <a id="38603" href="plfa.part2.Lambda.html#34215" class="InductiveConstructor">⊢ƛ</a> <a id="38606" class="Symbol">(</a><a id="38607" href="plfa.part2.Lambda.html#34215" class="InductiveConstructor">⊢ƛ</a> <a id="38610" class="Symbol">(</a><a id="38611" href="plfa.part2.Lambda.html#34215" class="InductiveConstructor">⊢ƛ</a> <a id="38614" class="Symbol">(</a><a id="38615" href="plfa.part2.Lambda.html#34215" class="InductiveConstructor">⊢ƛ</a> <a id="38618" class="Symbol">(</a><a id="38619" href="plfa.part2.Lambda.html#34136" class="InductiveConstructor">⊢`</a> <a id="38622" href="plfa.part2.Lambda.html#38673" class="Function">∋m</a> <a id="38625" href="plfa.part2.Lambda.html#34322" class="InductiveConstructor Operator">·</a> <a id="38627" href="plfa.part2.Lambda.html#34136" class="InductiveConstructor">⊢`</a> <a id="38630" href="plfa.part2.Lambda.html#38737" class="Function">∋s</a> <a id="38633" href="plfa.part2.Lambda.html#34322" class="InductiveConstructor Operator">·</a> <a id="38635" class="Symbol">(</a><a id="38636" href="plfa.part2.Lambda.html#34136" class="InductiveConstructor">⊢`</a> <a id="38639" href="plfa.part2.Lambda.html#38710" class="Function">∋n</a> <a id="38642" href="plfa.part2.Lambda.html#34322" class="InductiveConstructor Operator">·</a> <a id="38644" href="plfa.part2.Lambda.html#34136" class="InductiveConstructor">⊢`</a> <a id="38647" href="plfa.part2.Lambda.html#38737" class="Function">∋s</a> <a id="38650" href="plfa.part2.Lambda.html#34322" class="InductiveConstructor Operator">·</a> <a id="38652" href="plfa.part2.Lambda.html#34136" class="InductiveConstructor">⊢`</a> <a id="38655" href="plfa.part2.Lambda.html#38754" class="Function">∋z</a><a id="38657" class="Symbol">)))))</a>
  <a id="38665" class="Keyword">where</a>
  <a id="38673" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#38673" class="Function">∋m</a> <a id="38676" class="Symbol">=</a> <a id="38678" href="plfa.part2.Lambda.html#33025" class="InductiveConstructor">S</a> <a id="38680" class="Symbol">(λ())</a> <a id="38686" class="Symbol">(</a><a id="38687" href="plfa.part2.Lambda.html#33025" class="InductiveConstructor">S</a> <a id="38689" class="Symbol">(λ())</a> <a id="38695" class="Symbol">(</a><a id="38696" href="plfa.part2.Lambda.html#33025" class="InductiveConstructor">S</a> <a id="38698" class="Symbol">(λ())</a> <a id="38704" href="plfa.part2.Lambda.html#32959" class="InductiveConstructor">Z</a><a id="38705" class="Symbol">))</a>
  <a id="38710" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#38710" class="Function">∋n</a> <a id="38713" class="Symbol">=</a> <a id="38715" href="plfa.part2.Lambda.html#33025" class="InductiveConstructor">S</a> <a id="38717" class="Symbol">(λ())</a> <a id="38723" class="Symbol">(</a><a id="38724" href="plfa.part2.Lambda.html#33025" class="InductiveConstructor">S</a> <a id="38726" class="Symbol">(λ())</a> <a id="38732" href="plfa.part2.Lambda.html#32959" class="InductiveConstructor">Z</a><a id="38733" class="Symbol">)</a>
  <a id="38737" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#38737" class="Function">∋s</a> <a id="38740" class="Symbol">=</a> <a id="38742" href="plfa.part2.Lambda.html#33025" class="InductiveConstructor">S</a> <a id="38744" class="Symbol">(λ())</a> <a id="38750" href="plfa.part2.Lambda.html#32959" class="InductiveConstructor">Z</a>
  <a id="38754" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#38754" class="Function">∋z</a> <a id="38757" class="Symbol">=</a> <a id="38759" href="plfa.part2.Lambda.html#32959" class="InductiveConstructor">Z</a>

<a id="⊢sucᶜ"></a><a id="38762" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#38762" class="Function">⊢sucᶜ</a> <a id="38768" class="Symbol">:</a> <a id="38770" class="Symbol">∀</a> <a id="38772" class="Symbol">{</a><a id="38773" href="plfa.part2.Lambda.html#38773" class="Bound">Γ</a><a id="38774" class="Symbol">}</a> <a id="38776" class="Symbol">→</a> <a id="38778" href="plfa.part2.Lambda.html#38773" class="Bound">Γ</a> <a id="38780" href="plfa.part2.Lambda.html#34080" class="Datatype Operator">⊢</a> <a id="38782" href="plfa.part2.Lambda.html#5938" class="Function">sucᶜ</a> <a id="38787" href="plfa.part2.Lambda.html#34080" class="Datatype Operator">⦂</a> <a id="38789" href="plfa.part2.Lambda.html#30070" class="InductiveConstructor">`ℕ</a> <a id="38792" href="plfa.part2.Lambda.html#30043" class="InductiveConstructor Operator">⇒</a> <a id="38794" href="plfa.part2.Lambda.html#30070" class="InductiveConstructor">`ℕ</a>
<a id="38797" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#38762" class="Function">⊢sucᶜ</a> <a id="38803" class="Symbol">=</a> <a id="38805" href="plfa.part2.Lambda.html#34215" class="InductiveConstructor">⊢ƛ</a> <a id="38808" class="Symbol">(</a><a id="38809" href="plfa.part2.Lambda.html#34500" class="InductiveConstructor">⊢suc</a> <a id="38814" class="Symbol">(</a><a id="38815" href="plfa.part2.Lambda.html#34136" class="InductiveConstructor">⊢`</a> <a id="38818" href="plfa.part2.Lambda.html#38833" class="Function">∋n</a><a id="38820" class="Symbol">))</a>
  <a id="38825" class="Keyword">where</a>
  <a id="38833" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#38833" class="Function">∋n</a> <a id="38836" class="Symbol">=</a> <a id="38838" href="plfa.part2.Lambda.html#32959" class="InductiveConstructor">Z</a>

<a id="⊢2+2ᶜ"></a><a id="38841" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#38841" class="Function">⊢2+2ᶜ</a> <a id="38847" class="Symbol">:</a> <a id="38849" href="plfa.part2.Lambda.html#31704" class="InductiveConstructor">∅</a> <a id="38851" href="plfa.part2.Lambda.html#34080" class="Datatype Operator">⊢</a> <a id="38853" href="plfa.part2.Lambda.html#5834" class="Function">plusᶜ</a> <a id="38859" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="38861" href="plfa.part2.Lambda.html#5773" class="Function">twoᶜ</a> <a id="38866" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="38868" href="plfa.part2.Lambda.html#5773" class="Function">twoᶜ</a> <a id="38873" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="38875" href="plfa.part2.Lambda.html#5938" class="Function">sucᶜ</a> <a id="38880" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="38882" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a> <a id="38888" href="plfa.part2.Lambda.html#34080" class="Datatype Operator">⦂</a> <a id="38890" href="plfa.part2.Lambda.html#30070" class="InductiveConstructor">`ℕ</a>
<a id="38893" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#38841" class="Function">⊢2+2ᶜ</a> <a id="38899" class="Symbol">=</a> <a id="38901" href="plfa.part2.Lambda.html#38543" class="Function">⊢plusᶜ</a> <a id="38908" href="plfa.part2.Lambda.html#34322" class="InductiveConstructor Operator">·</a> <a id="38910" href="plfa.part2.Lambda.html#37370" class="Function">⊢twoᶜ</a> <a id="38916" href="plfa.part2.Lambda.html#34322" class="InductiveConstructor Operator">·</a> <a id="38918" href="plfa.part2.Lambda.html#37370" class="Function">⊢twoᶜ</a> <a id="38924" href="plfa.part2.Lambda.html#34322" class="InductiveConstructor Operator">·</a> <a id="38926" href="plfa.part2.Lambda.html#38762" class="Function">⊢sucᶜ</a> <a id="38932" href="plfa.part2.Lambda.html#34322" class="InductiveConstructor Operator">·</a> <a id="38934" href="plfa.part2.Lambda.html#34431" class="InductiveConstructor">⊢zero</a>
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
{% raw %}<pre class="Agda"><a id="∋-injective"></a><a id="40250" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#40250" class="Function">∋-injective</a> <a id="40262" class="Symbol">:</a> <a id="40264" class="Symbol">∀</a> <a id="40266" class="Symbol">{</a><a id="40267" href="plfa.part2.Lambda.html#40267" class="Bound">Γ</a> <a id="40269" href="plfa.part2.Lambda.html#40269" class="Bound">x</a> <a id="40271" href="plfa.part2.Lambda.html#40271" class="Bound">A</a> <a id="40273" href="plfa.part2.Lambda.html#40273" class="Bound">B</a><a id="40274" class="Symbol">}</a> <a id="40276" class="Symbol">→</a> <a id="40278" href="plfa.part2.Lambda.html#40267" class="Bound">Γ</a> <a id="40280" href="plfa.part2.Lambda.html#32916" class="Datatype Operator">∋</a> <a id="40282" href="plfa.part2.Lambda.html#40269" class="Bound">x</a> <a id="40284" href="plfa.part2.Lambda.html#32916" class="Datatype Operator">⦂</a> <a id="40286" href="plfa.part2.Lambda.html#40271" class="Bound">A</a> <a id="40288" class="Symbol">→</a> <a id="40290" href="plfa.part2.Lambda.html#40267" class="Bound">Γ</a> <a id="40292" href="plfa.part2.Lambda.html#32916" class="Datatype Operator">∋</a> <a id="40294" href="plfa.part2.Lambda.html#40269" class="Bound">x</a> <a id="40296" href="plfa.part2.Lambda.html#32916" class="Datatype Operator">⦂</a> <a id="40298" href="plfa.part2.Lambda.html#40273" class="Bound">B</a> <a id="40300" class="Symbol">→</a> <a id="40302" href="plfa.part2.Lambda.html#40271" class="Bound">A</a> <a id="40304" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="40306" href="plfa.part2.Lambda.html#40273" class="Bound">B</a>
<a id="40308" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#40250" class="Function">∋-injective</a> <a id="40320" href="plfa.part2.Lambda.html#32959" class="InductiveConstructor">Z</a>        <a id="40329" href="plfa.part2.Lambda.html#32959" class="InductiveConstructor">Z</a>          <a id="40340" class="Symbol">=</a>  <a id="40343" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>
<a id="40348" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#40250" class="Function">∋-injective</a> <a id="40360" href="plfa.part2.Lambda.html#32959" class="InductiveConstructor">Z</a>        <a id="40369" class="Symbol">(</a><a id="40370" href="plfa.part2.Lambda.html#33025" class="InductiveConstructor">S</a> <a id="40372" href="plfa.part2.Lambda.html#40372" class="Bound">x≢</a> <a id="40375" class="Symbol">_)</a>   <a id="40380" class="Symbol">=</a>  <a id="40383" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html#294" class="Function">⊥-elim</a> <a id="40390" class="Symbol">(</a><a id="40391" href="plfa.part2.Lambda.html#40372" class="Bound">x≢</a> <a id="40394" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a><a id="40398" class="Symbol">)</a>
<a id="40400" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#40250" class="Function">∋-injective</a> <a id="40412" class="Symbol">(</a><a id="40413" href="plfa.part2.Lambda.html#33025" class="InductiveConstructor">S</a> <a id="40415" href="plfa.part2.Lambda.html#40415" class="Bound">x≢</a> <a id="40418" class="Symbol">_)</a> <a id="40421" href="plfa.part2.Lambda.html#32959" class="InductiveConstructor">Z</a>          <a id="40432" class="Symbol">=</a>  <a id="40435" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html#294" class="Function">⊥-elim</a> <a id="40442" class="Symbol">(</a><a id="40443" href="plfa.part2.Lambda.html#40415" class="Bound">x≢</a> <a id="40446" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a><a id="40450" class="Symbol">)</a>
<a id="40452" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#40250" class="Function">∋-injective</a> <a id="40464" class="Symbol">(</a><a id="40465" href="plfa.part2.Lambda.html#33025" class="InductiveConstructor">S</a> <a id="40467" class="Symbol">_</a> <a id="40469" href="plfa.part2.Lambda.html#40469" class="Bound">∋x</a><a id="40471" class="Symbol">)</a> <a id="40473" class="Symbol">(</a><a id="40474" href="plfa.part2.Lambda.html#33025" class="InductiveConstructor">S</a> <a id="40476" class="Symbol">_</a> <a id="40478" href="plfa.part2.Lambda.html#40478" class="Bound">∋x′</a><a id="40481" class="Symbol">)</a>  <a id="40484" class="Symbol">=</a>  <a id="40487" href="plfa.part2.Lambda.html#40250" class="Function">∋-injective</a> <a id="40499" href="plfa.part2.Lambda.html#40469" class="Bound">∋x</a> <a id="40502" href="plfa.part2.Lambda.html#40478" class="Bound">∋x′</a>
</pre>{% endraw %}
The typing relation `Γ ⊢ M ⦂ A` is not injective. For example, in any `Γ`
the term `ƛ "x" ⇒ "x"` has type `A ⇒ A` for any type `A`.

### Non-examples

We can also show that terms are _not_ typeable.  For example, here is
a formal proof that it is not possible to type the term
`` `zero · `suc `zero ``.  It cannot be typed, because doing so
requires that the first term in the application is both a natural and
a function:

{% raw %}<pre class="Agda"><a id="nope₁"></a><a id="40939" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#40939" class="Function">nope₁</a> <a id="40945" class="Symbol">:</a> <a id="40947" class="Symbol">∀</a> <a id="40949" class="Symbol">{</a><a id="40950" href="plfa.part2.Lambda.html#40950" class="Bound">A</a><a id="40951" class="Symbol">}</a> <a id="40953" class="Symbol">→</a> <a id="40955" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#535" class="Function Operator">¬</a> <a id="40957" class="Symbol">(</a><a id="40958" href="plfa.part2.Lambda.html#31704" class="InductiveConstructor">∅</a> <a id="40960" href="plfa.part2.Lambda.html#34080" class="Datatype Operator">⊢</a> <a id="40962" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a> <a id="40968" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="40970" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="40975" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a> <a id="40981" href="plfa.part2.Lambda.html#34080" class="Datatype Operator">⦂</a> <a id="40983" href="plfa.part2.Lambda.html#40950" class="Bound">A</a><a id="40984" class="Symbol">)</a>
<a id="40986" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#40939" class="Function">nope₁</a> <a id="40992" class="Symbol">(()</a> <a id="40996" href="plfa.part2.Lambda.html#34322" class="InductiveConstructor Operator">·</a> <a id="40998" class="Symbol">_)</a>
</pre>{% endraw %}
As a second example, here is a formal proof that it is not possible to
type `` ƛ "x" ⇒ ` "x" · ` "x" ``. It cannot be typed, because
doing so requires types `A` and `B` such that `A ⇒ B ≡ A`:

{% raw %}<pre class="Agda"><a id="nope₂"></a><a id="41203" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#41203" class="Function">nope₂</a> <a id="41209" class="Symbol">:</a> <a id="41211" class="Symbol">∀</a> <a id="41213" class="Symbol">{</a><a id="41214" href="plfa.part2.Lambda.html#41214" class="Bound">A</a><a id="41215" class="Symbol">}</a> <a id="41217" class="Symbol">→</a> <a id="41219" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#535" class="Function Operator">¬</a> <a id="41221" class="Symbol">(</a><a id="41222" href="plfa.part2.Lambda.html#31704" class="InductiveConstructor">∅</a> <a id="41224" href="plfa.part2.Lambda.html#34080" class="Datatype Operator">⊢</a> <a id="41226" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">ƛ</a> <a id="41228" class="String">&quot;x&quot;</a> <a id="41232" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a> <a id="41234" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="41236" class="String">&quot;x&quot;</a> <a id="41240" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="41242" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="41244" class="String">&quot;x&quot;</a> <a id="41248" href="plfa.part2.Lambda.html#34080" class="Datatype Operator">⦂</a> <a id="41250" href="plfa.part2.Lambda.html#41214" class="Bound">A</a><a id="41251" class="Symbol">)</a>
<a id="41253" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#41203" class="Function">nope₂</a> <a id="41259" class="Symbol">(</a><a id="41260" href="plfa.part2.Lambda.html#34215" class="InductiveConstructor">⊢ƛ</a> <a id="41263" class="Symbol">(</a><a id="41264" href="plfa.part2.Lambda.html#34136" class="InductiveConstructor">⊢`</a> <a id="41267" href="plfa.part2.Lambda.html#41267" class="Bound">∋x</a> <a id="41270" href="plfa.part2.Lambda.html#34322" class="InductiveConstructor Operator">·</a> <a id="41272" href="plfa.part2.Lambda.html#34136" class="InductiveConstructor">⊢`</a> <a id="41275" href="plfa.part2.Lambda.html#41275" class="Bound">∋x′</a><a id="41278" class="Symbol">))</a>  <a id="41282" class="Symbol">=</a>  <a id="41285" href="plfa.part2.Lambda.html#41330" class="Function">contradiction</a> <a id="41299" class="Symbol">(</a><a id="41300" href="plfa.part2.Lambda.html#40250" class="Function">∋-injective</a> <a id="41312" href="plfa.part2.Lambda.html#41267" class="Bound">∋x</a> <a id="41315" href="plfa.part2.Lambda.html#41275" class="Bound">∋x′</a><a id="41318" class="Symbol">)</a>
  <a id="41322" class="Keyword">where</a>
  <a id="41330" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#41330" class="Function">contradiction</a> <a id="41344" class="Symbol">:</a> <a id="41346" class="Symbol">∀</a> <a id="41348" class="Symbol">{</a><a id="41349" href="plfa.part2.Lambda.html#41349" class="Bound">A</a> <a id="41351" href="plfa.part2.Lambda.html#41351" class="Bound">B</a><a id="41352" class="Symbol">}</a> <a id="41354" class="Symbol">→</a> <a id="41356" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#535" class="Function Operator">¬</a> <a id="41358" class="Symbol">(</a><a id="41359" href="plfa.part2.Lambda.html#41349" class="Bound">A</a> <a id="41361" href="plfa.part2.Lambda.html#30043" class="InductiveConstructor Operator">⇒</a> <a id="41363" href="plfa.part2.Lambda.html#41351" class="Bound">B</a> <a id="41365" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="41367" href="plfa.part2.Lambda.html#41349" class="Bound">A</a><a id="41368" class="Symbol">)</a>
  <a id="41372" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#41330" class="Function">contradiction</a> <a id="41386" class="Symbol">()</a>
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

{% raw %}<pre class="Agda"><a id="42065" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}

#### Exercise `mulᶜ-type` (practice)

Using the term `mulᶜ` you defined earlier, write out the derivation
showing that it is well typed.

{% raw %}<pre class="Agda"><a id="42236" class="Comment">-- Your code goes here</a>
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
