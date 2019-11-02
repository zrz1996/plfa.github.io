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
<a id="3747" class="Keyword">infixl</a> <a id="3754" class="Number">7</a>  <a id="3757" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#34332" class="InductiveConstructor Operator">_·_</a>
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
      (ƛ "z" ⇒ sucᶜ · (sucᶜ · ` "z")) · `zero
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

{% raw %}<pre class="Agda"><a id="15539" class="Keyword">infix</a> <a id="15545" class="Number">9</a> <a id="15547" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#15556" class="Function Operator">_[_:=_]</a>

<a id="_[_:=_]"></a><a id="15556" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#15556" class="Function Operator">_[_:=_]</a> <a id="15564" class="Symbol">:</a> <a id="15566" href="plfa.part2.Lambda.html#3796" class="Datatype">Term</a> <a id="15571" class="Symbol">→</a> <a id="15573" href="plfa.part2.Lambda.html#3695" class="Function">Id</a> <a id="15576" class="Symbol">→</a> <a id="15578" href="plfa.part2.Lambda.html#3796" class="Datatype">Term</a> <a id="15583" class="Symbol">→</a> <a id="15585" href="plfa.part2.Lambda.html#3796" class="Datatype">Term</a>
<a id="15590" class="Symbol">(</a><a id="15591" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3815" class="InductiveConstructor Operator">`</a> <a id="15593" href="plfa.part2.Lambda.html#15593" class="Bound">x</a><a id="15594" class="Symbol">)</a> <a id="15596" href="plfa.part2.Lambda.html#15556" class="Function Operator">[</a> <a id="15598" href="plfa.part2.Lambda.html#15598" class="Bound">y</a> <a id="15600" href="plfa.part2.Lambda.html#15556" class="Function Operator">:=</a> <a id="15603" href="plfa.part2.Lambda.html#15603" class="Bound">V</a> <a id="15605" href="plfa.part2.Lambda.html#15556" class="Function Operator">]</a> <a id="15607" class="Keyword">with</a> <a id="15612" href="plfa.part2.Lambda.html#15593" class="Bound">x</a> <a id="15614" href="https://agda.github.io/agda-stdlib/v1.1/Data.String.Properties.html#2569" class="Function Operator">≟</a> <a id="15616" href="plfa.part2.Lambda.html#15598" class="Bound">y</a>
<a id="15618" class="Symbol">...</a> <a id="15622" class="Symbol">|</a> <a id="15624" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#641" class="InductiveConstructor">yes</a> <a id="15628" class="Symbol">_</a>          <a id="15639" class="Symbol">=</a>  <a id="15642" class="Bound">V</a>
<a id="15644" class="Symbol">...</a> <a id="15648" class="Symbol">|</a> <a id="15650" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#668" class="InductiveConstructor">no</a>  <a id="15654" class="Symbol">_</a>          <a id="15665" class="Symbol">=</a>  <a id="15668" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3815" class="InductiveConstructor Operator">`</a> <a id="15670" class="Bound">x</a>
<a id="15672" class="Symbol">(</a><a id="15673" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3854" class="InductiveConstructor Operator">ƛ</a> <a id="15675" href="plfa.part2.Lambda.html#15675" class="Bound">x</a> <a id="15677" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a> <a id="15679" href="plfa.part2.Lambda.html#15679" class="Bound">N</a><a id="15680" class="Symbol">)</a> <a id="15682" href="plfa.part2.Lambda.html#15556" class="Function Operator">[</a> <a id="15684" href="plfa.part2.Lambda.html#15684" class="Bound">y</a> <a id="15686" href="plfa.part2.Lambda.html#15556" class="Function Operator">:=</a> <a id="15689" href="plfa.part2.Lambda.html#15689" class="Bound">V</a> <a id="15691" href="plfa.part2.Lambda.html#15556" class="Function Operator">]</a> <a id="15693" class="Keyword">with</a> <a id="15698" href="plfa.part2.Lambda.html#15675" class="Bound">x</a> <a id="15700" href="https://agda.github.io/agda-stdlib/v1.1/Data.String.Properties.html#2569" class="Function Operator">≟</a> <a id="15702" href="plfa.part2.Lambda.html#15684" class="Bound">y</a>
<a id="15704" class="Symbol">...</a> <a id="15708" class="Symbol">|</a> <a id="15710" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#641" class="InductiveConstructor">yes</a> <a id="15714" class="Symbol">_</a>          <a id="15725" class="Symbol">=</a>  <a id="15728" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3854" class="InductiveConstructor Operator">ƛ</a> <a id="15730" class="Bound">x</a> <a id="15732" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a> <a id="15734" class="Bound">N</a>
<a id="15736" class="Symbol">...</a> <a id="15740" class="Symbol">|</a> <a id="15742" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#668" class="InductiveConstructor">no</a>  <a id="15746" class="Symbol">_</a>          <a id="15757" class="Symbol">=</a>  <a id="15760" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3854" class="InductiveConstructor Operator">ƛ</a> <a id="15762" class="Bound">x</a> <a id="15764" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a> <a id="15766" class="Bound">N</a> <a id="15768" href="plfa.part2.Lambda.html#15556" class="Function Operator">[</a> <a id="15770" class="Bound">y</a> <a id="15772" href="plfa.part2.Lambda.html#15556" class="Function Operator">:=</a> <a id="15775" class="Bound">V</a> <a id="15777" href="plfa.part2.Lambda.html#15556" class="Function Operator">]</a>
<a id="15779" class="Symbol">(</a><a id="15780" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#15780" class="Bound">L</a> <a id="15782" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="15784" href="plfa.part2.Lambda.html#15784" class="Bound">M</a><a id="15785" class="Symbol">)</a> <a id="15787" href="plfa.part2.Lambda.html#15556" class="Function Operator">[</a> <a id="15789" href="plfa.part2.Lambda.html#15789" class="Bound">y</a> <a id="15791" href="plfa.part2.Lambda.html#15556" class="Function Operator">:=</a> <a id="15794" href="plfa.part2.Lambda.html#15794" class="Bound">V</a> <a id="15796" href="plfa.part2.Lambda.html#15556" class="Function Operator">]</a>   <a id="15800" class="Symbol">=</a>  <a id="15803" href="plfa.part2.Lambda.html#15780" class="Bound">L</a> <a id="15805" href="plfa.part2.Lambda.html#15556" class="Function Operator">[</a> <a id="15807" href="plfa.part2.Lambda.html#15789" class="Bound">y</a> <a id="15809" href="plfa.part2.Lambda.html#15556" class="Function Operator">:=</a> <a id="15812" href="plfa.part2.Lambda.html#15794" class="Bound">V</a> <a id="15814" href="plfa.part2.Lambda.html#15556" class="Function Operator">]</a> <a id="15816" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="15818" href="plfa.part2.Lambda.html#15784" class="Bound">M</a> <a id="15820" href="plfa.part2.Lambda.html#15556" class="Function Operator">[</a> <a id="15822" href="plfa.part2.Lambda.html#15789" class="Bound">y</a> <a id="15824" href="plfa.part2.Lambda.html#15556" class="Function Operator">:=</a> <a id="15827" href="plfa.part2.Lambda.html#15794" class="Bound">V</a> <a id="15829" href="plfa.part2.Lambda.html#15556" class="Function Operator">]</a>
<a id="15831" class="Symbol">(</a><a id="15832" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3948" class="InductiveConstructor">`zero</a><a id="15837" class="Symbol">)</a> <a id="15839" href="plfa.part2.Lambda.html#15556" class="Function Operator">[</a> <a id="15841" href="plfa.part2.Lambda.html#15841" class="Bound">y</a> <a id="15843" href="plfa.part2.Lambda.html#15556" class="Function Operator">:=</a> <a id="15846" href="plfa.part2.Lambda.html#15846" class="Bound">V</a> <a id="15848" href="plfa.part2.Lambda.html#15556" class="Function Operator">]</a>   <a id="15852" class="Symbol">=</a>  <a id="15855" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a>
<a id="15861" class="Symbol">(</a><a id="15862" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3982" class="InductiveConstructor Operator">`suc</a> <a id="15867" href="plfa.part2.Lambda.html#15867" class="Bound">M</a><a id="15868" class="Symbol">)</a> <a id="15870" href="plfa.part2.Lambda.html#15556" class="Function Operator">[</a> <a id="15872" href="plfa.part2.Lambda.html#15872" class="Bound">y</a> <a id="15874" href="plfa.part2.Lambda.html#15556" class="Function Operator">:=</a> <a id="15877" href="plfa.part2.Lambda.html#15877" class="Bound">V</a> <a id="15879" href="plfa.part2.Lambda.html#15556" class="Function Operator">]</a>  <a id="15882" class="Symbol">=</a>  <a id="15885" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="15890" href="plfa.part2.Lambda.html#15867" class="Bound">M</a> <a id="15892" href="plfa.part2.Lambda.html#15556" class="Function Operator">[</a> <a id="15894" href="plfa.part2.Lambda.html#15872" class="Bound">y</a> <a id="15896" href="plfa.part2.Lambda.html#15556" class="Function Operator">:=</a> <a id="15899" href="plfa.part2.Lambda.html#15877" class="Bound">V</a> <a id="15901" href="plfa.part2.Lambda.html#15556" class="Function Operator">]</a>
<a id="15903" class="Symbol">(</a><a id="15904" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#4023" class="InductiveConstructor Operator">case</a> <a id="15909" href="plfa.part2.Lambda.html#15909" class="Bound">L</a> <a id="15911" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">[zero⇒</a> <a id="15918" href="plfa.part2.Lambda.html#15918" class="Bound">M</a> <a id="15920" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">|suc</a> <a id="15925" href="plfa.part2.Lambda.html#15925" class="Bound">x</a> <a id="15927" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">⇒</a> <a id="15929" href="plfa.part2.Lambda.html#15929" class="Bound">N</a> <a id="15931" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">]</a><a id="15932" class="Symbol">)</a> <a id="15934" href="plfa.part2.Lambda.html#15556" class="Function Operator">[</a> <a id="15936" href="plfa.part2.Lambda.html#15936" class="Bound">y</a> <a id="15938" href="plfa.part2.Lambda.html#15556" class="Function Operator">:=</a> <a id="15941" href="plfa.part2.Lambda.html#15941" class="Bound">V</a> <a id="15943" href="plfa.part2.Lambda.html#15556" class="Function Operator">]</a> <a id="15945" class="Keyword">with</a> <a id="15950" href="plfa.part2.Lambda.html#15925" class="Bound">x</a> <a id="15952" href="https://agda.github.io/agda-stdlib/v1.1/Data.String.Properties.html#2569" class="Function Operator">≟</a> <a id="15954" href="plfa.part2.Lambda.html#15936" class="Bound">y</a>
<a id="15956" class="Symbol">...</a> <a id="15960" class="Symbol">|</a> <a id="15962" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#641" class="InductiveConstructor">yes</a> <a id="15966" class="Symbol">_</a>          <a id="15977" class="Symbol">=</a>  <a id="15980" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#4023" class="InductiveConstructor Operator">case</a> <a id="15985" class="Bound">L</a> <a id="15987" href="plfa.part2.Lambda.html#15556" class="Function Operator">[</a> <a id="15989" class="Bound">y</a> <a id="15991" href="plfa.part2.Lambda.html#15556" class="Function Operator">:=</a> <a id="15994" class="Bound">V</a> <a id="15996" href="plfa.part2.Lambda.html#15556" class="Function Operator">]</a> <a id="15998" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">[zero⇒</a> <a id="16005" class="Bound">M</a> <a id="16007" href="plfa.part2.Lambda.html#15556" class="Function Operator">[</a> <a id="16009" class="Bound">y</a> <a id="16011" href="plfa.part2.Lambda.html#15556" class="Function Operator">:=</a> <a id="16014" class="Bound">V</a> <a id="16016" href="plfa.part2.Lambda.html#15556" class="Function Operator">]</a> <a id="16018" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">|suc</a> <a id="16023" class="Bound">x</a> <a id="16025" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">⇒</a> <a id="16027" class="Bound">N</a> <a id="16029" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">]</a>
<a id="16031" class="Symbol">...</a> <a id="16035" class="Symbol">|</a> <a id="16037" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#668" class="InductiveConstructor">no</a>  <a id="16041" class="Symbol">_</a>          <a id="16052" class="Symbol">=</a>  <a id="16055" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#4023" class="InductiveConstructor Operator">case</a> <a id="16060" class="Bound">L</a> <a id="16062" href="plfa.part2.Lambda.html#15556" class="Function Operator">[</a> <a id="16064" class="Bound">y</a> <a id="16066" href="plfa.part2.Lambda.html#15556" class="Function Operator">:=</a> <a id="16069" class="Bound">V</a> <a id="16071" href="plfa.part2.Lambda.html#15556" class="Function Operator">]</a> <a id="16073" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">[zero⇒</a> <a id="16080" class="Bound">M</a> <a id="16082" href="plfa.part2.Lambda.html#15556" class="Function Operator">[</a> <a id="16084" class="Bound">y</a> <a id="16086" href="plfa.part2.Lambda.html#15556" class="Function Operator">:=</a> <a id="16089" class="Bound">V</a> <a id="16091" href="plfa.part2.Lambda.html#15556" class="Function Operator">]</a> <a id="16093" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">|suc</a> <a id="16098" class="Bound">x</a> <a id="16100" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">⇒</a> <a id="16102" class="Bound">N</a> <a id="16104" href="plfa.part2.Lambda.html#15556" class="Function Operator">[</a> <a id="16106" class="Bound">y</a> <a id="16108" href="plfa.part2.Lambda.html#15556" class="Function Operator">:=</a> <a id="16111" class="Bound">V</a> <a id="16113" href="plfa.part2.Lambda.html#15556" class="Function Operator">]</a> <a id="16115" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">]</a>
<a id="16117" class="Symbol">(</a><a id="16118" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#4083" class="InductiveConstructor Operator">μ</a> <a id="16120" href="plfa.part2.Lambda.html#16120" class="Bound">x</a> <a id="16122" href="plfa.part2.Lambda.html#4083" class="InductiveConstructor Operator">⇒</a> <a id="16124" href="plfa.part2.Lambda.html#16124" class="Bound">N</a><a id="16125" class="Symbol">)</a> <a id="16127" href="plfa.part2.Lambda.html#15556" class="Function Operator">[</a> <a id="16129" href="plfa.part2.Lambda.html#16129" class="Bound">y</a> <a id="16131" href="plfa.part2.Lambda.html#15556" class="Function Operator">:=</a> <a id="16134" href="plfa.part2.Lambda.html#16134" class="Bound">V</a> <a id="16136" href="plfa.part2.Lambda.html#15556" class="Function Operator">]</a> <a id="16138" class="Keyword">with</a> <a id="16143" href="plfa.part2.Lambda.html#16120" class="Bound">x</a> <a id="16145" href="https://agda.github.io/agda-stdlib/v1.1/Data.String.Properties.html#2569" class="Function Operator">≟</a> <a id="16147" href="plfa.part2.Lambda.html#16129" class="Bound">y</a>
<a id="16149" class="Symbol">...</a> <a id="16153" class="Symbol">|</a> <a id="16155" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#641" class="InductiveConstructor">yes</a> <a id="16159" class="Symbol">_</a>          <a id="16170" class="Symbol">=</a>  <a id="16173" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#4083" class="InductiveConstructor Operator">μ</a> <a id="16175" class="Bound">x</a> <a id="16177" href="plfa.part2.Lambda.html#4083" class="InductiveConstructor Operator">⇒</a> <a id="16179" class="Bound">N</a>
<a id="16181" class="Symbol">...</a> <a id="16185" class="Symbol">|</a> <a id="16187" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#668" class="InductiveConstructor">no</a>  <a id="16191" class="Symbol">_</a>          <a id="16202" class="Symbol">=</a>  <a id="16205" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#4083" class="InductiveConstructor Operator">μ</a> <a id="16207" class="Bound">x</a> <a id="16209" href="plfa.part2.Lambda.html#4083" class="InductiveConstructor Operator">⇒</a> <a id="16211" class="Bound">N</a> <a id="16213" href="plfa.part2.Lambda.html#15556" class="Function Operator">[</a> <a id="16215" class="Bound">y</a> <a id="16217" href="plfa.part2.Lambda.html#15556" class="Function Operator">:=</a> <a id="16220" class="Bound">V</a> <a id="16222" href="plfa.part2.Lambda.html#15556" class="Function Operator">]</a>
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

{% raw %}<pre class="Agda"><a id="16989" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#16989" class="Function">_</a> <a id="16991" class="Symbol">:</a> <a id="16993" class="Symbol">(</a><a id="16994" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">ƛ</a> <a id="16996" class="String">&quot;z&quot;</a> <a id="17000" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a> <a id="17002" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="17004" class="String">&quot;s&quot;</a> <a id="17008" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="17010" class="Symbol">(</a><a id="17011" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="17013" class="String">&quot;s&quot;</a> <a id="17017" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="17019" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="17021" class="String">&quot;z&quot;</a><a id="17024" class="Symbol">))</a> <a id="17027" href="plfa.part2.Lambda.html#15556" class="Function Operator">[</a> <a id="17029" class="String">&quot;s&quot;</a> <a id="17033" href="plfa.part2.Lambda.html#15556" class="Function Operator">:=</a> <a id="17036" href="plfa.part2.Lambda.html#5938" class="Function">sucᶜ</a> <a id="17041" href="plfa.part2.Lambda.html#15556" class="Function Operator">]</a> <a id="17043" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="17045" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">ƛ</a> <a id="17047" class="String">&quot;z&quot;</a> <a id="17051" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a> <a id="17053" href="plfa.part2.Lambda.html#5938" class="Function">sucᶜ</a> <a id="17058" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="17060" class="Symbol">(</a><a id="17061" href="plfa.part2.Lambda.html#5938" class="Function">sucᶜ</a> <a id="17066" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="17068" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="17070" class="String">&quot;z&quot;</a><a id="17073" class="Symbol">)</a>
<a id="17075" class="Symbol">_</a> <a id="17077" class="Symbol">=</a> <a id="17079" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>

<a id="17085" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#17085" class="Function">_</a> <a id="17087" class="Symbol">:</a> <a id="17089" class="Symbol">(</a><a id="17090" href="plfa.part2.Lambda.html#5938" class="Function">sucᶜ</a> <a id="17095" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="17097" class="Symbol">(</a><a id="17098" href="plfa.part2.Lambda.html#5938" class="Function">sucᶜ</a> <a id="17103" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="17105" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="17107" class="String">&quot;z&quot;</a><a id="17110" class="Symbol">))</a> <a id="17113" href="plfa.part2.Lambda.html#15556" class="Function Operator">[</a> <a id="17115" class="String">&quot;z&quot;</a> <a id="17119" href="plfa.part2.Lambda.html#15556" class="Function Operator">:=</a> <a id="17122" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a> <a id="17128" href="plfa.part2.Lambda.html#15556" class="Function Operator">]</a> <a id="17130" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="17132" href="plfa.part2.Lambda.html#5938" class="Function">sucᶜ</a> <a id="17137" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="17139" class="Symbol">(</a><a id="17140" href="plfa.part2.Lambda.html#5938" class="Function">sucᶜ</a> <a id="17145" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="17147" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a><a id="17152" class="Symbol">)</a>
<a id="17154" class="Symbol">_</a> <a id="17156" class="Symbol">=</a> <a id="17158" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>

<a id="17164" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#17164" class="Function">_</a> <a id="17166" class="Symbol">:</a> <a id="17168" class="Symbol">(</a><a id="17169" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">ƛ</a> <a id="17171" class="String">&quot;x&quot;</a> <a id="17175" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a> <a id="17177" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="17179" class="String">&quot;y&quot;</a><a id="17182" class="Symbol">)</a> <a id="17184" href="plfa.part2.Lambda.html#15556" class="Function Operator">[</a> <a id="17186" class="String">&quot;y&quot;</a> <a id="17190" href="plfa.part2.Lambda.html#15556" class="Function Operator">:=</a> <a id="17193" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a> <a id="17199" href="plfa.part2.Lambda.html#15556" class="Function Operator">]</a> <a id="17201" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="17203" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">ƛ</a> <a id="17205" class="String">&quot;x&quot;</a> <a id="17209" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a> <a id="17211" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a>
<a id="17217" class="Symbol">_</a> <a id="17219" class="Symbol">=</a> <a id="17221" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>

<a id="17227" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#17227" class="Function">_</a> <a id="17229" class="Symbol">:</a> <a id="17231" class="Symbol">(</a><a id="17232" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">ƛ</a> <a id="17234" class="String">&quot;x&quot;</a> <a id="17238" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a> <a id="17240" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="17242" class="String">&quot;x&quot;</a><a id="17245" class="Symbol">)</a> <a id="17247" href="plfa.part2.Lambda.html#15556" class="Function Operator">[</a> <a id="17249" class="String">&quot;x&quot;</a> <a id="17253" href="plfa.part2.Lambda.html#15556" class="Function Operator">:=</a> <a id="17256" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a> <a id="17262" href="plfa.part2.Lambda.html#15556" class="Function Operator">]</a> <a id="17264" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="17266" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">ƛ</a> <a id="17268" class="String">&quot;x&quot;</a> <a id="17272" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a> <a id="17274" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="17276" class="String">&quot;x&quot;</a>
<a id="17280" class="Symbol">_</a> <a id="17282" class="Symbol">=</a> <a id="17284" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>

<a id="17290" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#17290" class="Function">_</a> <a id="17292" class="Symbol">:</a> <a id="17294" class="Symbol">(</a><a id="17295" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">ƛ</a> <a id="17297" class="String">&quot;y&quot;</a> <a id="17301" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a> <a id="17303" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="17305" class="String">&quot;y&quot;</a><a id="17308" class="Symbol">)</a> <a id="17310" href="plfa.part2.Lambda.html#15556" class="Function Operator">[</a> <a id="17312" class="String">&quot;x&quot;</a> <a id="17316" href="plfa.part2.Lambda.html#15556" class="Function Operator">:=</a> <a id="17319" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a> <a id="17325" href="plfa.part2.Lambda.html#15556" class="Function Operator">]</a> <a id="17327" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="17329" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">ƛ</a> <a id="17331" class="String">&quot;y&quot;</a> <a id="17335" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a> <a id="17337" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="17339" class="String">&quot;y&quot;</a>
<a id="17343" class="Symbol">_</a> <a id="17345" class="Symbol">=</a> <a id="17347" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>
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

{% raw %}<pre class="Agda"><a id="17970" class="Comment">-- Your code goes here</a>
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

{% raw %}<pre class="Agda"><a id="20178" class="Keyword">infix</a> <a id="20184" class="Number">4</a> <a id="20186" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#20197" class="Datatype Operator">_—→_</a>

<a id="20192" class="Keyword">data</a> <a id="_—→_"></a><a id="20197" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#20197" class="Datatype Operator">_—→_</a> <a id="20202" class="Symbol">:</a> <a id="20204" href="plfa.part2.Lambda.html#3796" class="Datatype">Term</a> <a id="20209" class="Symbol">→</a> <a id="20211" href="plfa.part2.Lambda.html#3796" class="Datatype">Term</a> <a id="20216" class="Symbol">→</a> <a id="20218" class="PrimitiveType">Set</a> <a id="20222" class="Keyword">where</a>

  <a id="_—→_.ξ-·₁"></a><a id="20231" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#20231" class="InductiveConstructor">ξ-·₁</a> <a id="20236" class="Symbol">:</a> <a id="20238" class="Symbol">∀</a> <a id="20240" class="Symbol">{</a><a id="20241" href="plfa.part2.Lambda.html#20241" class="Bound">L</a> <a id="20243" href="plfa.part2.Lambda.html#20243" class="Bound">L′</a> <a id="20246" href="plfa.part2.Lambda.html#20246" class="Bound">M</a><a id="20247" class="Symbol">}</a>
    <a id="20253" class="Symbol">→</a> <a id="20255" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#20241" class="Bound">L</a> <a id="20257" href="plfa.part2.Lambda.html#20197" class="Datatype Operator">—→</a> <a id="20260" href="plfa.part2.Lambda.html#20243" class="Bound">L′</a>
      <a id="20269" class="Comment">-----------------</a>
    <a id="20291" class="Symbol">→</a> <a id="20293" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#20241" class="Bound">L</a> <a id="20295" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="20297" href="plfa.part2.Lambda.html#20246" class="Bound">M</a> <a id="20299" href="plfa.part2.Lambda.html#20197" class="Datatype Operator">—→</a> <a id="20302" href="plfa.part2.Lambda.html#20243" class="Bound">L′</a> <a id="20305" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="20307" href="plfa.part2.Lambda.html#20246" class="Bound">M</a>

  <a id="_—→_.ξ-·₂"></a><a id="20312" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#20312" class="InductiveConstructor">ξ-·₂</a> <a id="20317" class="Symbol">:</a> <a id="20319" class="Symbol">∀</a> <a id="20321" class="Symbol">{</a><a id="20322" href="plfa.part2.Lambda.html#20322" class="Bound">V</a> <a id="20324" href="plfa.part2.Lambda.html#20324" class="Bound">M</a> <a id="20326" href="plfa.part2.Lambda.html#20326" class="Bound">M′</a><a id="20328" class="Symbol">}</a>
    <a id="20334" class="Symbol">→</a> <a id="20336" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#12171" class="Datatype">Value</a> <a id="20342" href="plfa.part2.Lambda.html#20322" class="Bound">V</a>
    <a id="20348" class="Symbol">→</a> <a id="20350" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#20324" class="Bound">M</a> <a id="20352" href="plfa.part2.Lambda.html#20197" class="Datatype Operator">—→</a> <a id="20355" href="plfa.part2.Lambda.html#20326" class="Bound">M′</a>
      <a id="20364" class="Comment">-----------------</a>
    <a id="20386" class="Symbol">→</a> <a id="20388" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#20322" class="Bound">V</a> <a id="20390" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="20392" href="plfa.part2.Lambda.html#20324" class="Bound">M</a> <a id="20394" href="plfa.part2.Lambda.html#20197" class="Datatype Operator">—→</a> <a id="20397" href="plfa.part2.Lambda.html#20322" class="Bound">V</a> <a id="20399" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="20401" href="plfa.part2.Lambda.html#20326" class="Bound">M′</a>

  <a id="_—→_.β-ƛ"></a><a id="20407" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#20407" class="InductiveConstructor">β-ƛ</a> <a id="20411" class="Symbol">:</a> <a id="20413" class="Symbol">∀</a> <a id="20415" class="Symbol">{</a><a id="20416" href="plfa.part2.Lambda.html#20416" class="Bound">x</a> <a id="20418" href="plfa.part2.Lambda.html#20418" class="Bound">N</a> <a id="20420" href="plfa.part2.Lambda.html#20420" class="Bound">V</a><a id="20421" class="Symbol">}</a>
    <a id="20427" class="Symbol">→</a> <a id="20429" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#12171" class="Datatype">Value</a> <a id="20435" href="plfa.part2.Lambda.html#20420" class="Bound">V</a>
      <a id="20443" class="Comment">------------------------------</a>
    <a id="20478" class="Symbol">→</a> <a id="20480" class="Symbol">(</a><a id="20481" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3854" class="InductiveConstructor Operator">ƛ</a> <a id="20483" href="plfa.part2.Lambda.html#20416" class="Bound">x</a> <a id="20485" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a> <a id="20487" href="plfa.part2.Lambda.html#20418" class="Bound">N</a><a id="20488" class="Symbol">)</a> <a id="20490" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="20492" href="plfa.part2.Lambda.html#20420" class="Bound">V</a> <a id="20494" href="plfa.part2.Lambda.html#20197" class="Datatype Operator">—→</a> <a id="20497" href="plfa.part2.Lambda.html#20418" class="Bound">N</a> <a id="20499" href="plfa.part2.Lambda.html#15556" class="Function Operator">[</a> <a id="20501" href="plfa.part2.Lambda.html#20416" class="Bound">x</a> <a id="20503" href="plfa.part2.Lambda.html#15556" class="Function Operator">:=</a> <a id="20506" href="plfa.part2.Lambda.html#20420" class="Bound">V</a> <a id="20508" href="plfa.part2.Lambda.html#15556" class="Function Operator">]</a>

  <a id="_—→_.ξ-suc"></a><a id="20513" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#20513" class="InductiveConstructor">ξ-suc</a> <a id="20519" class="Symbol">:</a> <a id="20521" class="Symbol">∀</a> <a id="20523" class="Symbol">{</a><a id="20524" href="plfa.part2.Lambda.html#20524" class="Bound">M</a> <a id="20526" href="plfa.part2.Lambda.html#20526" class="Bound">M′</a><a id="20528" class="Symbol">}</a>
    <a id="20534" class="Symbol">→</a> <a id="20536" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#20524" class="Bound">M</a> <a id="20538" href="plfa.part2.Lambda.html#20197" class="Datatype Operator">—→</a> <a id="20541" href="plfa.part2.Lambda.html#20526" class="Bound">M′</a>
      <a id="20550" class="Comment">------------------</a>
    <a id="20573" class="Symbol">→</a> <a id="20575" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3982" class="InductiveConstructor Operator">`suc</a> <a id="20580" href="plfa.part2.Lambda.html#20524" class="Bound">M</a> <a id="20582" href="plfa.part2.Lambda.html#20197" class="Datatype Operator">—→</a> <a id="20585" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="20590" href="plfa.part2.Lambda.html#20526" class="Bound">M′</a>

  <a id="_—→_.ξ-case"></a><a id="20596" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#20596" class="InductiveConstructor">ξ-case</a> <a id="20603" class="Symbol">:</a> <a id="20605" class="Symbol">∀</a> <a id="20607" class="Symbol">{</a><a id="20608" href="plfa.part2.Lambda.html#20608" class="Bound">x</a> <a id="20610" href="plfa.part2.Lambda.html#20610" class="Bound">L</a> <a id="20612" href="plfa.part2.Lambda.html#20612" class="Bound">L′</a> <a id="20615" href="plfa.part2.Lambda.html#20615" class="Bound">M</a> <a id="20617" href="plfa.part2.Lambda.html#20617" class="Bound">N</a><a id="20618" class="Symbol">}</a>
    <a id="20624" class="Symbol">→</a> <a id="20626" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#20610" class="Bound">L</a> <a id="20628" href="plfa.part2.Lambda.html#20197" class="Datatype Operator">—→</a> <a id="20631" href="plfa.part2.Lambda.html#20612" class="Bound">L′</a>
      <a id="20640" class="Comment">-----------------------------------------------------------------</a>
    <a id="20710" class="Symbol">→</a> <a id="20712" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#4023" class="InductiveConstructor Operator">case</a> <a id="20717" href="plfa.part2.Lambda.html#20610" class="Bound">L</a> <a id="20719" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">[zero⇒</a> <a id="20726" href="plfa.part2.Lambda.html#20615" class="Bound">M</a> <a id="20728" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">|suc</a> <a id="20733" href="plfa.part2.Lambda.html#20608" class="Bound">x</a> <a id="20735" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">⇒</a> <a id="20737" href="plfa.part2.Lambda.html#20617" class="Bound">N</a> <a id="20739" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">]</a> <a id="20741" href="plfa.part2.Lambda.html#20197" class="Datatype Operator">—→</a> <a id="20744" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">case</a> <a id="20749" href="plfa.part2.Lambda.html#20612" class="Bound">L′</a> <a id="20752" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">[zero⇒</a> <a id="20759" href="plfa.part2.Lambda.html#20615" class="Bound">M</a> <a id="20761" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">|suc</a> <a id="20766" href="plfa.part2.Lambda.html#20608" class="Bound">x</a> <a id="20768" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">⇒</a> <a id="20770" href="plfa.part2.Lambda.html#20617" class="Bound">N</a> <a id="20772" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">]</a>

  <a id="_—→_.β-zero"></a><a id="20777" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#20777" class="InductiveConstructor">β-zero</a> <a id="20784" class="Symbol">:</a> <a id="20786" class="Symbol">∀</a> <a id="20788" class="Symbol">{</a><a id="20789" href="plfa.part2.Lambda.html#20789" class="Bound">x</a> <a id="20791" href="plfa.part2.Lambda.html#20791" class="Bound">M</a> <a id="20793" href="plfa.part2.Lambda.html#20793" class="Bound">N</a><a id="20794" class="Symbol">}</a>
      <a id="20802" class="Comment">----------------------------------------</a>
    <a id="20847" class="Symbol">→</a> <a id="20849" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#4023" class="InductiveConstructor Operator">case</a> <a id="20854" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a> <a id="20860" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">[zero⇒</a> <a id="20867" href="plfa.part2.Lambda.html#20791" class="Bound">M</a> <a id="20869" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">|suc</a> <a id="20874" href="plfa.part2.Lambda.html#20789" class="Bound">x</a> <a id="20876" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">⇒</a> <a id="20878" href="plfa.part2.Lambda.html#20793" class="Bound">N</a> <a id="20880" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">]</a> <a id="20882" href="plfa.part2.Lambda.html#20197" class="Datatype Operator">—→</a> <a id="20885" href="plfa.part2.Lambda.html#20791" class="Bound">M</a>

  <a id="_—→_.β-suc"></a><a id="20890" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#20890" class="InductiveConstructor">β-suc</a> <a id="20896" class="Symbol">:</a> <a id="20898" class="Symbol">∀</a> <a id="20900" class="Symbol">{</a><a id="20901" href="plfa.part2.Lambda.html#20901" class="Bound">x</a> <a id="20903" href="plfa.part2.Lambda.html#20903" class="Bound">V</a> <a id="20905" href="plfa.part2.Lambda.html#20905" class="Bound">M</a> <a id="20907" href="plfa.part2.Lambda.html#20907" class="Bound">N</a><a id="20908" class="Symbol">}</a>
    <a id="20914" class="Symbol">→</a> <a id="20916" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#12171" class="Datatype">Value</a> <a id="20922" href="plfa.part2.Lambda.html#20903" class="Bound">V</a>
      <a id="20930" class="Comment">---------------------------------------------------</a>
    <a id="20986" class="Symbol">→</a> <a id="20988" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#4023" class="InductiveConstructor Operator">case</a> <a id="20993" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="20998" href="plfa.part2.Lambda.html#20903" class="Bound">V</a> <a id="21000" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">[zero⇒</a> <a id="21007" href="plfa.part2.Lambda.html#20905" class="Bound">M</a> <a id="21009" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">|suc</a> <a id="21014" href="plfa.part2.Lambda.html#20901" class="Bound">x</a> <a id="21016" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">⇒</a> <a id="21018" href="plfa.part2.Lambda.html#20907" class="Bound">N</a> <a id="21020" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">]</a> <a id="21022" href="plfa.part2.Lambda.html#20197" class="Datatype Operator">—→</a> <a id="21025" href="plfa.part2.Lambda.html#20907" class="Bound">N</a> <a id="21027" href="plfa.part2.Lambda.html#15556" class="Function Operator">[</a> <a id="21029" href="plfa.part2.Lambda.html#20901" class="Bound">x</a> <a id="21031" href="plfa.part2.Lambda.html#15556" class="Function Operator">:=</a> <a id="21034" href="plfa.part2.Lambda.html#20903" class="Bound">V</a> <a id="21036" href="plfa.part2.Lambda.html#15556" class="Function Operator">]</a>

  <a id="_—→_.β-μ"></a><a id="21041" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#21041" class="InductiveConstructor">β-μ</a> <a id="21045" class="Symbol">:</a> <a id="21047" class="Symbol">∀</a> <a id="21049" class="Symbol">{</a><a id="21050" href="plfa.part2.Lambda.html#21050" class="Bound">x</a> <a id="21052" href="plfa.part2.Lambda.html#21052" class="Bound">M</a><a id="21053" class="Symbol">}</a>
      <a id="21061" class="Comment">------------------------------</a>
    <a id="21096" class="Symbol">→</a> <a id="21098" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#4083" class="InductiveConstructor Operator">μ</a> <a id="21100" href="plfa.part2.Lambda.html#21050" class="Bound">x</a> <a id="21102" href="plfa.part2.Lambda.html#4083" class="InductiveConstructor Operator">⇒</a> <a id="21104" href="plfa.part2.Lambda.html#21052" class="Bound">M</a> <a id="21106" href="plfa.part2.Lambda.html#20197" class="Datatype Operator">—→</a> <a id="21109" href="plfa.part2.Lambda.html#21052" class="Bound">M</a> <a id="21111" href="plfa.part2.Lambda.html#15556" class="Function Operator">[</a> <a id="21113" href="plfa.part2.Lambda.html#21050" class="Bound">x</a> <a id="21115" href="plfa.part2.Lambda.html#15556" class="Function Operator">:=</a> <a id="21118" href="plfa.part2.Lambda.html#4083" class="InductiveConstructor Operator">μ</a> <a id="21120" href="plfa.part2.Lambda.html#21050" class="Bound">x</a> <a id="21122" href="plfa.part2.Lambda.html#4083" class="InductiveConstructor Operator">⇒</a> <a id="21124" href="plfa.part2.Lambda.html#21052" class="Bound">M</a> <a id="21126" href="plfa.part2.Lambda.html#15556" class="Function Operator">]</a>
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
{% raw %}<pre class="Agda"><a id="23122" class="Keyword">infix</a>  <a id="23129" class="Number">2</a> <a id="23131" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23187" class="Datatype Operator">_—↠_</a>
<a id="23136" class="Keyword">infix</a>  <a id="23143" class="Number">1</a> <a id="23145" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23337" class="Function Operator">begin_</a>
<a id="23152" class="Keyword">infixr</a> <a id="23159" class="Number">2</a> <a id="23161" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23261" class="InductiveConstructor Operator">_—→⟨_⟩_</a>
<a id="23169" class="Keyword">infix</a>  <a id="23176" class="Number">3</a> <a id="23178" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23220" class="InductiveConstructor Operator">_∎</a>

<a id="23182" class="Keyword">data</a> <a id="_—↠_"></a><a id="23187" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23187" class="Datatype Operator">_—↠_</a> <a id="23192" class="Symbol">:</a> <a id="23194" href="plfa.part2.Lambda.html#3796" class="Datatype">Term</a> <a id="23199" class="Symbol">→</a> <a id="23201" href="plfa.part2.Lambda.html#3796" class="Datatype">Term</a> <a id="23206" class="Symbol">→</a> <a id="23208" class="PrimitiveType">Set</a> <a id="23212" class="Keyword">where</a>
  <a id="_—↠_._∎"></a><a id="23220" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23220" class="InductiveConstructor Operator">_∎</a> <a id="23223" class="Symbol">:</a> <a id="23225" class="Symbol">∀</a> <a id="23227" href="plfa.part2.Lambda.html#23227" class="Bound">M</a>
      <a id="23235" class="Comment">---------</a>
    <a id="23249" class="Symbol">→</a> <a id="23251" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23227" class="Bound">M</a> <a id="23253" href="plfa.part2.Lambda.html#23187" class="Datatype Operator">—↠</a> <a id="23256" href="plfa.part2.Lambda.html#23227" class="Bound">M</a>

  <a id="_—↠_._—→⟨_⟩_"></a><a id="23261" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23261" class="InductiveConstructor Operator">_—→⟨_⟩_</a> <a id="23269" class="Symbol">:</a> <a id="23271" class="Symbol">∀</a> <a id="23273" href="plfa.part2.Lambda.html#23273" class="Bound">L</a> <a id="23275" class="Symbol">{</a><a id="23276" href="plfa.part2.Lambda.html#23276" class="Bound">M</a> <a id="23278" href="plfa.part2.Lambda.html#23278" class="Bound">N</a><a id="23279" class="Symbol">}</a>
    <a id="23285" class="Symbol">→</a> <a id="23287" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23273" class="Bound">L</a> <a id="23289" href="plfa.part2.Lambda.html#20197" class="Datatype Operator">—→</a> <a id="23292" href="plfa.part2.Lambda.html#23276" class="Bound">M</a>
    <a id="23298" class="Symbol">→</a> <a id="23300" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23276" class="Bound">M</a> <a id="23302" href="plfa.part2.Lambda.html#23187" class="Datatype Operator">—↠</a> <a id="23305" href="plfa.part2.Lambda.html#23278" class="Bound">N</a>
      <a id="23313" class="Comment">---------</a>
    <a id="23327" class="Symbol">→</a> <a id="23329" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23273" class="Bound">L</a> <a id="23331" href="plfa.part2.Lambda.html#23187" class="Datatype Operator">—↠</a> <a id="23334" href="plfa.part2.Lambda.html#23278" class="Bound">N</a>

<a id="begin_"></a><a id="23337" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23337" class="Function Operator">begin_</a> <a id="23344" class="Symbol">:</a> <a id="23346" class="Symbol">∀</a> <a id="23348" class="Symbol">{</a><a id="23349" href="plfa.part2.Lambda.html#23349" class="Bound">M</a> <a id="23351" href="plfa.part2.Lambda.html#23351" class="Bound">N</a><a id="23352" class="Symbol">}</a>
  <a id="23356" class="Symbol">→</a> <a id="23358" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23349" class="Bound">M</a> <a id="23360" href="plfa.part2.Lambda.html#23187" class="Datatype Operator">—↠</a> <a id="23363" href="plfa.part2.Lambda.html#23351" class="Bound">N</a>
    <a id="23369" class="Comment">------</a>
  <a id="23378" class="Symbol">→</a> <a id="23380" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23349" class="Bound">M</a> <a id="23382" href="plfa.part2.Lambda.html#23187" class="Datatype Operator">—↠</a> <a id="23385" href="plfa.part2.Lambda.html#23351" class="Bound">N</a>
<a id="23387" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23337" class="Function Operator">begin</a> <a id="23393" href="plfa.part2.Lambda.html#23393" class="Bound">M—↠N</a> <a id="23398" class="Symbol">=</a> <a id="23400" href="plfa.part2.Lambda.html#23393" class="Bound">M—↠N</a>
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
{% raw %}<pre class="Agda"><a id="24083" class="Keyword">data</a> <a id="_—↠′_"></a><a id="24088" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#24088" class="Datatype Operator">_—↠′_</a> <a id="24094" class="Symbol">:</a> <a id="24096" href="plfa.part2.Lambda.html#3796" class="Datatype">Term</a> <a id="24101" class="Symbol">→</a> <a id="24103" href="plfa.part2.Lambda.html#3796" class="Datatype">Term</a> <a id="24108" class="Symbol">→</a> <a id="24110" class="PrimitiveType">Set</a> <a id="24114" class="Keyword">where</a>

  <a id="_—↠′_.step′"></a><a id="24123" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#24123" class="InductiveConstructor">step′</a> <a id="24129" class="Symbol">:</a> <a id="24131" class="Symbol">∀</a> <a id="24133" class="Symbol">{</a><a id="24134" href="plfa.part2.Lambda.html#24134" class="Bound">M</a> <a id="24136" href="plfa.part2.Lambda.html#24136" class="Bound">N</a><a id="24137" class="Symbol">}</a>
    <a id="24143" class="Symbol">→</a> <a id="24145" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#24134" class="Bound">M</a> <a id="24147" href="plfa.part2.Lambda.html#20197" class="Datatype Operator">—→</a> <a id="24150" href="plfa.part2.Lambda.html#24136" class="Bound">N</a>
      <a id="24158" class="Comment">-------</a>
    <a id="24170" class="Symbol">→</a> <a id="24172" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#24134" class="Bound">M</a> <a id="24174" href="plfa.part2.Lambda.html#24088" class="Datatype Operator">—↠′</a> <a id="24178" href="plfa.part2.Lambda.html#24136" class="Bound">N</a>

  <a id="_—↠′_.refl′"></a><a id="24183" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#24183" class="InductiveConstructor">refl′</a> <a id="24189" class="Symbol">:</a> <a id="24191" class="Symbol">∀</a> <a id="24193" class="Symbol">{</a><a id="24194" href="plfa.part2.Lambda.html#24194" class="Bound">M</a><a id="24195" class="Symbol">}</a>
      <a id="24203" class="Comment">-------</a>
    <a id="24215" class="Symbol">→</a> <a id="24217" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#24194" class="Bound">M</a> <a id="24219" href="plfa.part2.Lambda.html#24088" class="Datatype Operator">—↠′</a> <a id="24223" href="plfa.part2.Lambda.html#24194" class="Bound">M</a>

  <a id="_—↠′_.trans′"></a><a id="24228" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#24228" class="InductiveConstructor">trans′</a> <a id="24235" class="Symbol">:</a> <a id="24237" class="Symbol">∀</a> <a id="24239" class="Symbol">{</a><a id="24240" href="plfa.part2.Lambda.html#24240" class="Bound">L</a> <a id="24242" href="plfa.part2.Lambda.html#24242" class="Bound">M</a> <a id="24244" href="plfa.part2.Lambda.html#24244" class="Bound">N</a><a id="24245" class="Symbol">}</a>
    <a id="24251" class="Symbol">→</a> <a id="24253" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#24240" class="Bound">L</a> <a id="24255" href="plfa.part2.Lambda.html#24088" class="Datatype Operator">—↠′</a> <a id="24259" href="plfa.part2.Lambda.html#24242" class="Bound">M</a>
    <a id="24265" class="Symbol">→</a> <a id="24267" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#24242" class="Bound">M</a> <a id="24269" href="plfa.part2.Lambda.html#24088" class="Datatype Operator">—↠′</a> <a id="24273" href="plfa.part2.Lambda.html#24244" class="Bound">N</a>
      <a id="24281" class="Comment">-------</a>
    <a id="24293" class="Symbol">→</a> <a id="24295" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#24240" class="Bound">L</a> <a id="24297" href="plfa.part2.Lambda.html#24088" class="Datatype Operator">—↠′</a> <a id="24301" href="plfa.part2.Lambda.html#24244" class="Bound">N</a>
</pre>{% endraw %}The three constructors specify, respectively, that `—↠′` includes `—→`
and is reflexive and transitive.  A good exercise is to show that
the two definitions are equivalent (indeed, one embeds in the other).

#### Exercise `—↠≲—↠′` (practice)

Show that the first notion of reflexive and transitive closure
above embeds into the second. Why are they not isomorphic?

{% raw %}<pre class="Agda"><a id="24677" class="Comment">-- Your code goes here</a>
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
{% raw %}<pre class="Agda"><a id="26247" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#26247" class="Function">_</a> <a id="26249" class="Symbol">:</a> <a id="26251" href="plfa.part2.Lambda.html#5773" class="Function">twoᶜ</a> <a id="26256" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="26258" href="plfa.part2.Lambda.html#5938" class="Function">sucᶜ</a> <a id="26263" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="26265" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a> <a id="26271" href="plfa.part2.Lambda.html#23187" class="Datatype Operator">—↠</a> <a id="26274" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="26279" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="26284" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a>
<a id="26290" class="Symbol">_</a> <a id="26292" class="Symbol">=</a>
  <a id="26296" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23337" class="Function Operator">begin</a>
    <a id="26306" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#5773" class="Function">twoᶜ</a> <a id="26311" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="26313" href="plfa.part2.Lambda.html#5938" class="Function">sucᶜ</a> <a id="26318" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="26320" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a>
  <a id="26328" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23261" class="InductiveConstructor Operator">—→⟨</a> <a id="26332" href="plfa.part2.Lambda.html#20231" class="InductiveConstructor">ξ-·₁</a> <a id="26337" class="Symbol">(</a><a id="26338" href="plfa.part2.Lambda.html#20407" class="InductiveConstructor">β-ƛ</a> <a id="26342" href="plfa.part2.Lambda.html#12199" class="InductiveConstructor">V-ƛ</a><a id="26345" class="Symbol">)</a> <a id="26347" href="plfa.part2.Lambda.html#23261" class="InductiveConstructor Operator">⟩</a>
    <a id="26353" class="Symbol">(</a><a id="26354" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3854" class="InductiveConstructor Operator">ƛ</a> <a id="26356" class="String">&quot;z&quot;</a> <a id="26360" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a> <a id="26362" href="plfa.part2.Lambda.html#5938" class="Function">sucᶜ</a> <a id="26367" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="26369" class="Symbol">(</a><a id="26370" href="plfa.part2.Lambda.html#5938" class="Function">sucᶜ</a> <a id="26375" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="26377" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="26379" class="String">&quot;z&quot;</a><a id="26382" class="Symbol">))</a> <a id="26385" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="26387" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a>
  <a id="26395" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23261" class="InductiveConstructor Operator">—→⟨</a> <a id="26399" href="plfa.part2.Lambda.html#20407" class="InductiveConstructor">β-ƛ</a> <a id="26403" href="plfa.part2.Lambda.html#12260" class="InductiveConstructor">V-zero</a> <a id="26410" href="plfa.part2.Lambda.html#23261" class="InductiveConstructor Operator">⟩</a>
    <a id="26416" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#5938" class="Function">sucᶜ</a> <a id="26421" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="26423" class="Symbol">(</a><a id="26424" href="plfa.part2.Lambda.html#5938" class="Function">sucᶜ</a> <a id="26429" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="26431" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a><a id="26436" class="Symbol">)</a>
  <a id="26440" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23261" class="InductiveConstructor Operator">—→⟨</a> <a id="26444" href="plfa.part2.Lambda.html#20312" class="InductiveConstructor">ξ-·₂</a> <a id="26449" href="plfa.part2.Lambda.html#12199" class="InductiveConstructor">V-ƛ</a> <a id="26453" class="Symbol">(</a><a id="26454" href="plfa.part2.Lambda.html#20407" class="InductiveConstructor">β-ƛ</a> <a id="26458" href="plfa.part2.Lambda.html#12260" class="InductiveConstructor">V-zero</a><a id="26464" class="Symbol">)</a> <a id="26466" href="plfa.part2.Lambda.html#23261" class="InductiveConstructor Operator">⟩</a>
    <a id="26472" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#5938" class="Function">sucᶜ</a> <a id="26477" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="26479" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="26484" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a>
  <a id="26492" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23261" class="InductiveConstructor Operator">—→⟨</a> <a id="26496" href="plfa.part2.Lambda.html#20407" class="InductiveConstructor">β-ƛ</a> <a id="26500" class="Symbol">(</a><a id="26501" href="plfa.part2.Lambda.html#12308" class="InductiveConstructor">V-suc</a> <a id="26507" href="plfa.part2.Lambda.html#12260" class="InductiveConstructor">V-zero</a><a id="26513" class="Symbol">)</a> <a id="26515" href="plfa.part2.Lambda.html#23261" class="InductiveConstructor Operator">⟩</a>
    <a id="26521" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3982" class="InductiveConstructor Operator">`suc</a> <a id="26526" class="Symbol">(</a><a id="26527" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="26532" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a><a id="26537" class="Symbol">)</a>
  <a id="26541" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23220" class="InductiveConstructor Operator">∎</a>
</pre>{% endraw %}
Here is a sample reduction demonstrating that two plus two is four:
{% raw %}<pre class="Agda"><a id="26620" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#26620" class="Function">_</a> <a id="26622" class="Symbol">:</a> <a id="26624" href="plfa.part2.Lambda.html#4558" class="Function">plus</a> <a id="26629" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="26631" href="plfa.part2.Lambda.html#4524" class="Function">two</a> <a id="26635" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="26637" href="plfa.part2.Lambda.html#4524" class="Function">two</a> <a id="26641" href="plfa.part2.Lambda.html#23187" class="Datatype Operator">—↠</a> <a id="26644" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="26649" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="26654" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="26659" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="26664" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a>
<a id="26670" class="Symbol">_</a> <a id="26672" class="Symbol">=</a>
  <a id="26676" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23337" class="Function Operator">begin</a>
    <a id="26686" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#4558" class="Function">plus</a> <a id="26691" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="26693" href="plfa.part2.Lambda.html#4524" class="Function">two</a> <a id="26697" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="26699" href="plfa.part2.Lambda.html#4524" class="Function">two</a>
  <a id="26705" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23261" class="InductiveConstructor Operator">—→⟨</a> <a id="26709" href="plfa.part2.Lambda.html#20231" class="InductiveConstructor">ξ-·₁</a> <a id="26714" class="Symbol">(</a><a id="26715" href="plfa.part2.Lambda.html#20231" class="InductiveConstructor">ξ-·₁</a> <a id="26720" href="plfa.part2.Lambda.html#21041" class="InductiveConstructor">β-μ</a><a id="26723" class="Symbol">)</a> <a id="26725" href="plfa.part2.Lambda.html#23261" class="InductiveConstructor Operator">⟩</a>
    <a id="26731" class="Symbol">(</a><a id="26732" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3854" class="InductiveConstructor Operator">ƛ</a> <a id="26734" class="String">&quot;m&quot;</a> <a id="26738" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a> <a id="26740" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">ƛ</a> <a id="26742" class="String">&quot;n&quot;</a> <a id="26746" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a>
      <a id="26754" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#4023" class="InductiveConstructor Operator">case</a> <a id="26759" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="26761" class="String">&quot;m&quot;</a> <a id="26765" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">[zero⇒</a> <a id="26772" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="26774" class="String">&quot;n&quot;</a> <a id="26778" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">|suc</a> <a id="26783" class="String">&quot;m&quot;</a> <a id="26787" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">⇒</a> <a id="26789" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="26794" class="Symbol">(</a><a id="26795" href="plfa.part2.Lambda.html#4558" class="Function">plus</a> <a id="26800" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="26802" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="26804" class="String">&quot;m&quot;</a> <a id="26808" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="26810" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="26812" class="String">&quot;n&quot;</a><a id="26815" class="Symbol">)</a> <a id="26817" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">]</a><a id="26818" class="Symbol">)</a>
        <a id="26828" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3900" class="InductiveConstructor Operator">·</a> <a id="26830" href="plfa.part2.Lambda.html#4524" class="Function">two</a> <a id="26834" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="26836" href="plfa.part2.Lambda.html#4524" class="Function">two</a>
  <a id="26842" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23261" class="InductiveConstructor Operator">—→⟨</a> <a id="26846" href="plfa.part2.Lambda.html#20231" class="InductiveConstructor">ξ-·₁</a> <a id="26851" class="Symbol">(</a><a id="26852" href="plfa.part2.Lambda.html#20407" class="InductiveConstructor">β-ƛ</a> <a id="26856" class="Symbol">(</a><a id="26857" href="plfa.part2.Lambda.html#12308" class="InductiveConstructor">V-suc</a> <a id="26863" class="Symbol">(</a><a id="26864" href="plfa.part2.Lambda.html#12308" class="InductiveConstructor">V-suc</a> <a id="26870" href="plfa.part2.Lambda.html#12260" class="InductiveConstructor">V-zero</a><a id="26876" class="Symbol">)))</a> <a id="26880" href="plfa.part2.Lambda.html#23261" class="InductiveConstructor Operator">⟩</a>
    <a id="26886" class="Symbol">(</a><a id="26887" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3854" class="InductiveConstructor Operator">ƛ</a> <a id="26889" class="String">&quot;n&quot;</a> <a id="26893" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a>
      <a id="26901" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#4023" class="InductiveConstructor Operator">case</a> <a id="26906" href="plfa.part2.Lambda.html#4524" class="Function">two</a> <a id="26910" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">[zero⇒</a> <a id="26917" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="26919" class="String">&quot;n&quot;</a> <a id="26923" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">|suc</a> <a id="26928" class="String">&quot;m&quot;</a> <a id="26932" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">⇒</a> <a id="26934" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="26939" class="Symbol">(</a><a id="26940" href="plfa.part2.Lambda.html#4558" class="Function">plus</a> <a id="26945" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="26947" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="26949" class="String">&quot;m&quot;</a> <a id="26953" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="26955" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="26957" class="String">&quot;n&quot;</a><a id="26960" class="Symbol">)</a> <a id="26962" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">]</a><a id="26963" class="Symbol">)</a>
         <a id="26974" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3900" class="InductiveConstructor Operator">·</a> <a id="26976" href="plfa.part2.Lambda.html#4524" class="Function">two</a>
  <a id="26982" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23261" class="InductiveConstructor Operator">—→⟨</a> <a id="26986" href="plfa.part2.Lambda.html#20407" class="InductiveConstructor">β-ƛ</a> <a id="26990" class="Symbol">(</a><a id="26991" href="plfa.part2.Lambda.html#12308" class="InductiveConstructor">V-suc</a> <a id="26997" class="Symbol">(</a><a id="26998" href="plfa.part2.Lambda.html#12308" class="InductiveConstructor">V-suc</a> <a id="27004" href="plfa.part2.Lambda.html#12260" class="InductiveConstructor">V-zero</a><a id="27010" class="Symbol">))</a> <a id="27013" href="plfa.part2.Lambda.html#23261" class="InductiveConstructor Operator">⟩</a>
    <a id="27019" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#4023" class="InductiveConstructor Operator">case</a> <a id="27024" href="plfa.part2.Lambda.html#4524" class="Function">two</a> <a id="27028" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">[zero⇒</a> <a id="27035" href="plfa.part2.Lambda.html#4524" class="Function">two</a> <a id="27039" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">|suc</a> <a id="27044" class="String">&quot;m&quot;</a> <a id="27048" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">⇒</a> <a id="27050" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="27055" class="Symbol">(</a><a id="27056" href="plfa.part2.Lambda.html#4558" class="Function">plus</a> <a id="27061" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="27063" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="27065" class="String">&quot;m&quot;</a> <a id="27069" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="27071" href="plfa.part2.Lambda.html#4524" class="Function">two</a><a id="27074" class="Symbol">)</a> <a id="27076" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">]</a>
  <a id="27080" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23261" class="InductiveConstructor Operator">—→⟨</a> <a id="27084" href="plfa.part2.Lambda.html#20890" class="InductiveConstructor">β-suc</a> <a id="27090" class="Symbol">(</a><a id="27091" href="plfa.part2.Lambda.html#12308" class="InductiveConstructor">V-suc</a> <a id="27097" href="plfa.part2.Lambda.html#12260" class="InductiveConstructor">V-zero</a><a id="27103" class="Symbol">)</a> <a id="27105" href="plfa.part2.Lambda.html#23261" class="InductiveConstructor Operator">⟩</a>
    <a id="27111" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3982" class="InductiveConstructor Operator">`suc</a> <a id="27116" class="Symbol">(</a><a id="27117" href="plfa.part2.Lambda.html#4558" class="Function">plus</a> <a id="27122" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="27124" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="27129" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a> <a id="27135" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="27137" href="plfa.part2.Lambda.html#4524" class="Function">two</a><a id="27140" class="Symbol">)</a>
  <a id="27144" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23261" class="InductiveConstructor Operator">—→⟨</a> <a id="27148" href="plfa.part2.Lambda.html#20513" class="InductiveConstructor">ξ-suc</a> <a id="27154" class="Symbol">(</a><a id="27155" href="plfa.part2.Lambda.html#20231" class="InductiveConstructor">ξ-·₁</a> <a id="27160" class="Symbol">(</a><a id="27161" href="plfa.part2.Lambda.html#20231" class="InductiveConstructor">ξ-·₁</a> <a id="27166" href="plfa.part2.Lambda.html#21041" class="InductiveConstructor">β-μ</a><a id="27169" class="Symbol">))</a> <a id="27172" href="plfa.part2.Lambda.html#23261" class="InductiveConstructor Operator">⟩</a>
    <a id="27178" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3982" class="InductiveConstructor Operator">`suc</a> <a id="27183" class="Symbol">((</a><a id="27185" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">ƛ</a> <a id="27187" class="String">&quot;m&quot;</a> <a id="27191" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a> <a id="27193" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">ƛ</a> <a id="27195" class="String">&quot;n&quot;</a> <a id="27199" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a>
      <a id="27207" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#4023" class="InductiveConstructor Operator">case</a> <a id="27212" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="27214" class="String">&quot;m&quot;</a> <a id="27218" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">[zero⇒</a> <a id="27225" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="27227" class="String">&quot;n&quot;</a> <a id="27231" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">|suc</a> <a id="27236" class="String">&quot;m&quot;</a> <a id="27240" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">⇒</a> <a id="27242" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="27247" class="Symbol">(</a><a id="27248" href="plfa.part2.Lambda.html#4558" class="Function">plus</a> <a id="27253" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="27255" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="27257" class="String">&quot;m&quot;</a> <a id="27261" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="27263" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="27265" class="String">&quot;n&quot;</a><a id="27268" class="Symbol">)</a> <a id="27270" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">]</a><a id="27271" class="Symbol">)</a>
        <a id="27281" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3900" class="InductiveConstructor Operator">·</a> <a id="27283" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="27288" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a> <a id="27294" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="27296" href="plfa.part2.Lambda.html#4524" class="Function">two</a><a id="27299" class="Symbol">)</a>
  <a id="27303" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23261" class="InductiveConstructor Operator">—→⟨</a> <a id="27307" href="plfa.part2.Lambda.html#20513" class="InductiveConstructor">ξ-suc</a> <a id="27313" class="Symbol">(</a><a id="27314" href="plfa.part2.Lambda.html#20231" class="InductiveConstructor">ξ-·₁</a> <a id="27319" class="Symbol">(</a><a id="27320" href="plfa.part2.Lambda.html#20407" class="InductiveConstructor">β-ƛ</a> <a id="27324" class="Symbol">(</a><a id="27325" href="plfa.part2.Lambda.html#12308" class="InductiveConstructor">V-suc</a> <a id="27331" href="plfa.part2.Lambda.html#12260" class="InductiveConstructor">V-zero</a><a id="27337" class="Symbol">)))</a> <a id="27341" href="plfa.part2.Lambda.html#23261" class="InductiveConstructor Operator">⟩</a>
    <a id="27347" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3982" class="InductiveConstructor Operator">`suc</a> <a id="27352" class="Symbol">((</a><a id="27354" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">ƛ</a> <a id="27356" class="String">&quot;n&quot;</a> <a id="27360" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a>
      <a id="27368" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#4023" class="InductiveConstructor Operator">case</a> <a id="27373" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="27378" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a> <a id="27384" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">[zero⇒</a> <a id="27391" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="27393" class="String">&quot;n&quot;</a> <a id="27397" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">|suc</a> <a id="27402" class="String">&quot;m&quot;</a> <a id="27406" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">⇒</a> <a id="27408" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="27413" class="Symbol">(</a><a id="27414" href="plfa.part2.Lambda.html#4558" class="Function">plus</a> <a id="27419" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="27421" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="27423" class="String">&quot;m&quot;</a> <a id="27427" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="27429" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="27431" class="String">&quot;n&quot;</a><a id="27434" class="Symbol">)</a> <a id="27436" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">]</a><a id="27437" class="Symbol">)</a>
        <a id="27447" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3900" class="InductiveConstructor Operator">·</a> <a id="27449" href="plfa.part2.Lambda.html#4524" class="Function">two</a><a id="27452" class="Symbol">)</a>
  <a id="27456" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23261" class="InductiveConstructor Operator">—→⟨</a> <a id="27460" href="plfa.part2.Lambda.html#20513" class="InductiveConstructor">ξ-suc</a> <a id="27466" class="Symbol">(</a><a id="27467" href="plfa.part2.Lambda.html#20407" class="InductiveConstructor">β-ƛ</a> <a id="27471" class="Symbol">(</a><a id="27472" href="plfa.part2.Lambda.html#12308" class="InductiveConstructor">V-suc</a> <a id="27478" class="Symbol">(</a><a id="27479" href="plfa.part2.Lambda.html#12308" class="InductiveConstructor">V-suc</a> <a id="27485" href="plfa.part2.Lambda.html#12260" class="InductiveConstructor">V-zero</a><a id="27491" class="Symbol">)))</a> <a id="27495" href="plfa.part2.Lambda.html#23261" class="InductiveConstructor Operator">⟩</a>
    <a id="27501" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3982" class="InductiveConstructor Operator">`suc</a> <a id="27506" class="Symbol">(</a><a id="27507" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">case</a> <a id="27512" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="27517" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a> <a id="27523" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">[zero⇒</a> <a id="27530" href="plfa.part2.Lambda.html#4524" class="Function">two</a> <a id="27534" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">|suc</a> <a id="27539" class="String">&quot;m&quot;</a> <a id="27543" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">⇒</a> <a id="27545" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="27550" class="Symbol">(</a><a id="27551" href="plfa.part2.Lambda.html#4558" class="Function">plus</a> <a id="27556" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="27558" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="27560" class="String">&quot;m&quot;</a> <a id="27564" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="27566" href="plfa.part2.Lambda.html#4524" class="Function">two</a><a id="27569" class="Symbol">)</a> <a id="27571" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">]</a><a id="27572" class="Symbol">)</a>
  <a id="27576" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23261" class="InductiveConstructor Operator">—→⟨</a> <a id="27580" href="plfa.part2.Lambda.html#20513" class="InductiveConstructor">ξ-suc</a> <a id="27586" class="Symbol">(</a><a id="27587" href="plfa.part2.Lambda.html#20890" class="InductiveConstructor">β-suc</a> <a id="27593" href="plfa.part2.Lambda.html#12260" class="InductiveConstructor">V-zero</a><a id="27599" class="Symbol">)</a> <a id="27601" href="plfa.part2.Lambda.html#23261" class="InductiveConstructor Operator">⟩</a>
    <a id="27607" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3982" class="InductiveConstructor Operator">`suc</a> <a id="27612" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="27617" class="Symbol">(</a><a id="27618" href="plfa.part2.Lambda.html#4558" class="Function">plus</a> <a id="27623" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="27625" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a> <a id="27631" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="27633" href="plfa.part2.Lambda.html#4524" class="Function">two</a><a id="27636" class="Symbol">)</a>
  <a id="27640" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23261" class="InductiveConstructor Operator">—→⟨</a> <a id="27644" href="plfa.part2.Lambda.html#20513" class="InductiveConstructor">ξ-suc</a> <a id="27650" class="Symbol">(</a><a id="27651" href="plfa.part2.Lambda.html#20513" class="InductiveConstructor">ξ-suc</a> <a id="27657" class="Symbol">(</a><a id="27658" href="plfa.part2.Lambda.html#20231" class="InductiveConstructor">ξ-·₁</a> <a id="27663" class="Symbol">(</a><a id="27664" href="plfa.part2.Lambda.html#20231" class="InductiveConstructor">ξ-·₁</a> <a id="27669" href="plfa.part2.Lambda.html#21041" class="InductiveConstructor">β-μ</a><a id="27672" class="Symbol">)))</a> <a id="27676" href="plfa.part2.Lambda.html#23261" class="InductiveConstructor Operator">⟩</a>
    <a id="27682" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3982" class="InductiveConstructor Operator">`suc</a> <a id="27687" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="27692" class="Symbol">((</a><a id="27694" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">ƛ</a> <a id="27696" class="String">&quot;m&quot;</a> <a id="27700" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a> <a id="27702" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">ƛ</a> <a id="27704" class="String">&quot;n&quot;</a> <a id="27708" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a>
      <a id="27716" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#4023" class="InductiveConstructor Operator">case</a> <a id="27721" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="27723" class="String">&quot;m&quot;</a> <a id="27727" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">[zero⇒</a> <a id="27734" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="27736" class="String">&quot;n&quot;</a> <a id="27740" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">|suc</a> <a id="27745" class="String">&quot;m&quot;</a> <a id="27749" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">⇒</a> <a id="27751" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="27756" class="Symbol">(</a><a id="27757" href="plfa.part2.Lambda.html#4558" class="Function">plus</a> <a id="27762" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="27764" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="27766" class="String">&quot;m&quot;</a> <a id="27770" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="27772" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="27774" class="String">&quot;n&quot;</a><a id="27777" class="Symbol">)</a> <a id="27779" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">]</a><a id="27780" class="Symbol">)</a>
        <a id="27790" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3900" class="InductiveConstructor Operator">·</a> <a id="27792" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a> <a id="27798" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="27800" href="plfa.part2.Lambda.html#4524" class="Function">two</a><a id="27803" class="Symbol">)</a>
  <a id="27807" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23261" class="InductiveConstructor Operator">—→⟨</a> <a id="27811" href="plfa.part2.Lambda.html#20513" class="InductiveConstructor">ξ-suc</a> <a id="27817" class="Symbol">(</a><a id="27818" href="plfa.part2.Lambda.html#20513" class="InductiveConstructor">ξ-suc</a> <a id="27824" class="Symbol">(</a><a id="27825" href="plfa.part2.Lambda.html#20231" class="InductiveConstructor">ξ-·₁</a> <a id="27830" class="Symbol">(</a><a id="27831" href="plfa.part2.Lambda.html#20407" class="InductiveConstructor">β-ƛ</a> <a id="27835" href="plfa.part2.Lambda.html#12260" class="InductiveConstructor">V-zero</a><a id="27841" class="Symbol">)))</a> <a id="27845" href="plfa.part2.Lambda.html#23261" class="InductiveConstructor Operator">⟩</a>
    <a id="27851" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3982" class="InductiveConstructor Operator">`suc</a> <a id="27856" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="27861" class="Symbol">((</a><a id="27863" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">ƛ</a> <a id="27865" class="String">&quot;n&quot;</a> <a id="27869" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a>
      <a id="27877" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#4023" class="InductiveConstructor Operator">case</a> <a id="27882" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a> <a id="27888" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">[zero⇒</a> <a id="27895" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="27897" class="String">&quot;n&quot;</a> <a id="27901" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">|suc</a> <a id="27906" class="String">&quot;m&quot;</a> <a id="27910" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">⇒</a> <a id="27912" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="27917" class="Symbol">(</a><a id="27918" href="plfa.part2.Lambda.html#4558" class="Function">plus</a> <a id="27923" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="27925" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="27927" class="String">&quot;m&quot;</a> <a id="27931" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="27933" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="27935" class="String">&quot;n&quot;</a><a id="27938" class="Symbol">)</a> <a id="27940" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">]</a><a id="27941" class="Symbol">)</a>
        <a id="27951" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3900" class="InductiveConstructor Operator">·</a> <a id="27953" href="plfa.part2.Lambda.html#4524" class="Function">two</a><a id="27956" class="Symbol">)</a>
  <a id="27960" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23261" class="InductiveConstructor Operator">—→⟨</a> <a id="27964" href="plfa.part2.Lambda.html#20513" class="InductiveConstructor">ξ-suc</a> <a id="27970" class="Symbol">(</a><a id="27971" href="plfa.part2.Lambda.html#20513" class="InductiveConstructor">ξ-suc</a> <a id="27977" class="Symbol">(</a><a id="27978" href="plfa.part2.Lambda.html#20407" class="InductiveConstructor">β-ƛ</a> <a id="27982" class="Symbol">(</a><a id="27983" href="plfa.part2.Lambda.html#12308" class="InductiveConstructor">V-suc</a> <a id="27989" class="Symbol">(</a><a id="27990" href="plfa.part2.Lambda.html#12308" class="InductiveConstructor">V-suc</a> <a id="27996" href="plfa.part2.Lambda.html#12260" class="InductiveConstructor">V-zero</a><a id="28002" class="Symbol">))))</a> <a id="28007" href="plfa.part2.Lambda.html#23261" class="InductiveConstructor Operator">⟩</a>
    <a id="28013" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3982" class="InductiveConstructor Operator">`suc</a> <a id="28018" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="28023" class="Symbol">(</a><a id="28024" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">case</a> <a id="28029" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a> <a id="28035" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">[zero⇒</a> <a id="28042" href="plfa.part2.Lambda.html#4524" class="Function">two</a> <a id="28046" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">|suc</a> <a id="28051" class="String">&quot;m&quot;</a> <a id="28055" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">⇒</a> <a id="28057" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="28062" class="Symbol">(</a><a id="28063" href="plfa.part2.Lambda.html#4558" class="Function">plus</a> <a id="28068" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="28070" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="28072" class="String">&quot;m&quot;</a> <a id="28076" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="28078" href="plfa.part2.Lambda.html#4524" class="Function">two</a><a id="28081" class="Symbol">)</a> <a id="28083" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">]</a><a id="28084" class="Symbol">)</a>
  <a id="28088" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23261" class="InductiveConstructor Operator">—→⟨</a> <a id="28092" href="plfa.part2.Lambda.html#20513" class="InductiveConstructor">ξ-suc</a> <a id="28098" class="Symbol">(</a><a id="28099" href="plfa.part2.Lambda.html#20513" class="InductiveConstructor">ξ-suc</a> <a id="28105" href="plfa.part2.Lambda.html#20777" class="InductiveConstructor">β-zero</a><a id="28111" class="Symbol">)</a> <a id="28113" href="plfa.part2.Lambda.html#23261" class="InductiveConstructor Operator">⟩</a>
    <a id="28119" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3982" class="InductiveConstructor Operator">`suc</a> <a id="28124" class="Symbol">(</a><a id="28125" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="28130" class="Symbol">(</a><a id="28131" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="28136" class="Symbol">(</a><a id="28137" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="28142" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a><a id="28147" class="Symbol">)))</a>
  <a id="28153" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23220" class="InductiveConstructor Operator">∎</a>
</pre>{% endraw %}
And here is a similar sample reduction for Church numerals:
{% raw %}<pre class="Agda"><a id="28224" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#28224" class="Function">_</a> <a id="28226" class="Symbol">:</a> <a id="28228" href="plfa.part2.Lambda.html#5834" class="Function">plusᶜ</a> <a id="28234" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="28236" href="plfa.part2.Lambda.html#5773" class="Function">twoᶜ</a> <a id="28241" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="28243" href="plfa.part2.Lambda.html#5773" class="Function">twoᶜ</a> <a id="28248" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="28250" href="plfa.part2.Lambda.html#5938" class="Function">sucᶜ</a> <a id="28255" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="28257" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a> <a id="28263" href="plfa.part2.Lambda.html#23187" class="Datatype Operator">—↠</a> <a id="28266" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="28271" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="28276" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="28281" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="28286" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a>
<a id="28292" class="Symbol">_</a> <a id="28294" class="Symbol">=</a>
  <a id="28298" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23337" class="Function Operator">begin</a>
    <a id="28308" class="Symbol">(</a><a id="28309" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3854" class="InductiveConstructor Operator">ƛ</a> <a id="28311" class="String">&quot;m&quot;</a> <a id="28315" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a> <a id="28317" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">ƛ</a> <a id="28319" class="String">&quot;n&quot;</a> <a id="28323" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a> <a id="28325" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">ƛ</a> <a id="28327" class="String">&quot;s&quot;</a> <a id="28331" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a> <a id="28333" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">ƛ</a> <a id="28335" class="String">&quot;z&quot;</a> <a id="28339" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a> <a id="28341" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="28343" class="String">&quot;m&quot;</a> <a id="28347" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="28349" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="28351" class="String">&quot;s&quot;</a> <a id="28355" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="28357" class="Symbol">(</a><a id="28358" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="28360" class="String">&quot;n&quot;</a> <a id="28364" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="28366" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="28368" class="String">&quot;s&quot;</a> <a id="28372" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="28374" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="28376" class="String">&quot;z&quot;</a><a id="28379" class="Symbol">))</a>
      <a id="28388" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3900" class="InductiveConstructor Operator">·</a> <a id="28390" href="plfa.part2.Lambda.html#5773" class="Function">twoᶜ</a> <a id="28395" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="28397" href="plfa.part2.Lambda.html#5773" class="Function">twoᶜ</a> <a id="28402" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="28404" href="plfa.part2.Lambda.html#5938" class="Function">sucᶜ</a> <a id="28409" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="28411" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a>
  <a id="28419" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23261" class="InductiveConstructor Operator">—→⟨</a> <a id="28423" href="plfa.part2.Lambda.html#20231" class="InductiveConstructor">ξ-·₁</a> <a id="28428" class="Symbol">(</a><a id="28429" href="plfa.part2.Lambda.html#20231" class="InductiveConstructor">ξ-·₁</a> <a id="28434" class="Symbol">(</a><a id="28435" href="plfa.part2.Lambda.html#20231" class="InductiveConstructor">ξ-·₁</a> <a id="28440" class="Symbol">(</a><a id="28441" href="plfa.part2.Lambda.html#20407" class="InductiveConstructor">β-ƛ</a> <a id="28445" href="plfa.part2.Lambda.html#12199" class="InductiveConstructor">V-ƛ</a><a id="28448" class="Symbol">)))</a> <a id="28452" href="plfa.part2.Lambda.html#23261" class="InductiveConstructor Operator">⟩</a>
    <a id="28458" class="Symbol">(</a><a id="28459" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3854" class="InductiveConstructor Operator">ƛ</a> <a id="28461" class="String">&quot;n&quot;</a> <a id="28465" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a> <a id="28467" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">ƛ</a> <a id="28469" class="String">&quot;s&quot;</a> <a id="28473" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a> <a id="28475" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">ƛ</a> <a id="28477" class="String">&quot;z&quot;</a> <a id="28481" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a> <a id="28483" href="plfa.part2.Lambda.html#5773" class="Function">twoᶜ</a> <a id="28488" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="28490" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="28492" class="String">&quot;s&quot;</a> <a id="28496" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="28498" class="Symbol">(</a><a id="28499" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="28501" class="String">&quot;n&quot;</a> <a id="28505" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="28507" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="28509" class="String">&quot;s&quot;</a> <a id="28513" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="28515" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="28517" class="String">&quot;z&quot;</a><a id="28520" class="Symbol">))</a>
      <a id="28529" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3900" class="InductiveConstructor Operator">·</a> <a id="28531" href="plfa.part2.Lambda.html#5773" class="Function">twoᶜ</a> <a id="28536" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="28538" href="plfa.part2.Lambda.html#5938" class="Function">sucᶜ</a> <a id="28543" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="28545" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a>
  <a id="28553" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23261" class="InductiveConstructor Operator">—→⟨</a> <a id="28557" href="plfa.part2.Lambda.html#20231" class="InductiveConstructor">ξ-·₁</a> <a id="28562" class="Symbol">(</a><a id="28563" href="plfa.part2.Lambda.html#20231" class="InductiveConstructor">ξ-·₁</a> <a id="28568" class="Symbol">(</a><a id="28569" href="plfa.part2.Lambda.html#20407" class="InductiveConstructor">β-ƛ</a> <a id="28573" href="plfa.part2.Lambda.html#12199" class="InductiveConstructor">V-ƛ</a><a id="28576" class="Symbol">))</a> <a id="28579" href="plfa.part2.Lambda.html#23261" class="InductiveConstructor Operator">⟩</a>
    <a id="28585" class="Symbol">(</a><a id="28586" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3854" class="InductiveConstructor Operator">ƛ</a> <a id="28588" class="String">&quot;s&quot;</a> <a id="28592" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a> <a id="28594" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">ƛ</a> <a id="28596" class="String">&quot;z&quot;</a> <a id="28600" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a> <a id="28602" href="plfa.part2.Lambda.html#5773" class="Function">twoᶜ</a> <a id="28607" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="28609" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="28611" class="String">&quot;s&quot;</a> <a id="28615" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="28617" class="Symbol">(</a><a id="28618" href="plfa.part2.Lambda.html#5773" class="Function">twoᶜ</a> <a id="28623" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="28625" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="28627" class="String">&quot;s&quot;</a> <a id="28631" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="28633" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="28635" class="String">&quot;z&quot;</a><a id="28638" class="Symbol">))</a> <a id="28641" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="28643" href="plfa.part2.Lambda.html#5938" class="Function">sucᶜ</a> <a id="28648" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="28650" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a>
  <a id="28658" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23261" class="InductiveConstructor Operator">—→⟨</a> <a id="28662" href="plfa.part2.Lambda.html#20231" class="InductiveConstructor">ξ-·₁</a> <a id="28667" class="Symbol">(</a><a id="28668" href="plfa.part2.Lambda.html#20407" class="InductiveConstructor">β-ƛ</a> <a id="28672" href="plfa.part2.Lambda.html#12199" class="InductiveConstructor">V-ƛ</a><a id="28675" class="Symbol">)</a> <a id="28677" href="plfa.part2.Lambda.html#23261" class="InductiveConstructor Operator">⟩</a>
    <a id="28683" class="Symbol">(</a><a id="28684" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3854" class="InductiveConstructor Operator">ƛ</a> <a id="28686" class="String">&quot;z&quot;</a> <a id="28690" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a> <a id="28692" href="plfa.part2.Lambda.html#5773" class="Function">twoᶜ</a> <a id="28697" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="28699" href="plfa.part2.Lambda.html#5938" class="Function">sucᶜ</a> <a id="28704" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="28706" class="Symbol">(</a><a id="28707" href="plfa.part2.Lambda.html#5773" class="Function">twoᶜ</a> <a id="28712" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="28714" href="plfa.part2.Lambda.html#5938" class="Function">sucᶜ</a> <a id="28719" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="28721" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="28723" class="String">&quot;z&quot;</a><a id="28726" class="Symbol">))</a> <a id="28729" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="28731" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a>
  <a id="28739" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23261" class="InductiveConstructor Operator">—→⟨</a> <a id="28743" href="plfa.part2.Lambda.html#20407" class="InductiveConstructor">β-ƛ</a> <a id="28747" href="plfa.part2.Lambda.html#12260" class="InductiveConstructor">V-zero</a> <a id="28754" href="plfa.part2.Lambda.html#23261" class="InductiveConstructor Operator">⟩</a>
    <a id="28760" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#5773" class="Function">twoᶜ</a> <a id="28765" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="28767" href="plfa.part2.Lambda.html#5938" class="Function">sucᶜ</a> <a id="28772" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="28774" class="Symbol">(</a><a id="28775" href="plfa.part2.Lambda.html#5773" class="Function">twoᶜ</a> <a id="28780" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="28782" href="plfa.part2.Lambda.html#5938" class="Function">sucᶜ</a> <a id="28787" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="28789" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a><a id="28794" class="Symbol">)</a>
  <a id="28798" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23261" class="InductiveConstructor Operator">—→⟨</a> <a id="28802" href="plfa.part2.Lambda.html#20231" class="InductiveConstructor">ξ-·₁</a> <a id="28807" class="Symbol">(</a><a id="28808" href="plfa.part2.Lambda.html#20407" class="InductiveConstructor">β-ƛ</a> <a id="28812" href="plfa.part2.Lambda.html#12199" class="InductiveConstructor">V-ƛ</a><a id="28815" class="Symbol">)</a> <a id="28817" href="plfa.part2.Lambda.html#23261" class="InductiveConstructor Operator">⟩</a>
    <a id="28823" class="Symbol">(</a><a id="28824" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3854" class="InductiveConstructor Operator">ƛ</a> <a id="28826" class="String">&quot;z&quot;</a> <a id="28830" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a> <a id="28832" href="plfa.part2.Lambda.html#5938" class="Function">sucᶜ</a> <a id="28837" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="28839" class="Symbol">(</a><a id="28840" href="plfa.part2.Lambda.html#5938" class="Function">sucᶜ</a> <a id="28845" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="28847" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="28849" class="String">&quot;z&quot;</a><a id="28852" class="Symbol">))</a> <a id="28855" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="28857" class="Symbol">(</a><a id="28858" href="plfa.part2.Lambda.html#5773" class="Function">twoᶜ</a> <a id="28863" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="28865" href="plfa.part2.Lambda.html#5938" class="Function">sucᶜ</a> <a id="28870" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="28872" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a><a id="28877" class="Symbol">)</a>
  <a id="28881" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23261" class="InductiveConstructor Operator">—→⟨</a> <a id="28885" href="plfa.part2.Lambda.html#20312" class="InductiveConstructor">ξ-·₂</a> <a id="28890" href="plfa.part2.Lambda.html#12199" class="InductiveConstructor">V-ƛ</a> <a id="28894" class="Symbol">(</a><a id="28895" href="plfa.part2.Lambda.html#20231" class="InductiveConstructor">ξ-·₁</a> <a id="28900" class="Symbol">(</a><a id="28901" href="plfa.part2.Lambda.html#20407" class="InductiveConstructor">β-ƛ</a> <a id="28905" href="plfa.part2.Lambda.html#12199" class="InductiveConstructor">V-ƛ</a><a id="28908" class="Symbol">))</a> <a id="28911" href="plfa.part2.Lambda.html#23261" class="InductiveConstructor Operator">⟩</a>
    <a id="28917" class="Symbol">(</a><a id="28918" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3854" class="InductiveConstructor Operator">ƛ</a> <a id="28920" class="String">&quot;z&quot;</a> <a id="28924" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a> <a id="28926" href="plfa.part2.Lambda.html#5938" class="Function">sucᶜ</a> <a id="28931" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="28933" class="Symbol">(</a><a id="28934" href="plfa.part2.Lambda.html#5938" class="Function">sucᶜ</a> <a id="28939" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="28941" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="28943" class="String">&quot;z&quot;</a><a id="28946" class="Symbol">))</a> <a id="28949" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="28951" class="Symbol">((</a><a id="28953" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">ƛ</a> <a id="28955" class="String">&quot;z&quot;</a> <a id="28959" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a> <a id="28961" href="plfa.part2.Lambda.html#5938" class="Function">sucᶜ</a> <a id="28966" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="28968" class="Symbol">(</a><a id="28969" href="plfa.part2.Lambda.html#5938" class="Function">sucᶜ</a> <a id="28974" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="28976" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="28978" class="String">&quot;z&quot;</a><a id="28981" class="Symbol">))</a> <a id="28984" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="28986" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a><a id="28991" class="Symbol">)</a>
  <a id="28995" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23261" class="InductiveConstructor Operator">—→⟨</a> <a id="28999" href="plfa.part2.Lambda.html#20312" class="InductiveConstructor">ξ-·₂</a> <a id="29004" href="plfa.part2.Lambda.html#12199" class="InductiveConstructor">V-ƛ</a> <a id="29008" class="Symbol">(</a><a id="29009" href="plfa.part2.Lambda.html#20407" class="InductiveConstructor">β-ƛ</a> <a id="29013" href="plfa.part2.Lambda.html#12260" class="InductiveConstructor">V-zero</a><a id="29019" class="Symbol">)</a> <a id="29021" href="plfa.part2.Lambda.html#23261" class="InductiveConstructor Operator">⟩</a>
    <a id="29027" class="Symbol">(</a><a id="29028" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3854" class="InductiveConstructor Operator">ƛ</a> <a id="29030" class="String">&quot;z&quot;</a> <a id="29034" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a> <a id="29036" href="plfa.part2.Lambda.html#5938" class="Function">sucᶜ</a> <a id="29041" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="29043" class="Symbol">(</a><a id="29044" href="plfa.part2.Lambda.html#5938" class="Function">sucᶜ</a> <a id="29049" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="29051" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="29053" class="String">&quot;z&quot;</a><a id="29056" class="Symbol">))</a> <a id="29059" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="29061" class="Symbol">(</a><a id="29062" href="plfa.part2.Lambda.html#5938" class="Function">sucᶜ</a> <a id="29067" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="29069" class="Symbol">(</a><a id="29070" href="plfa.part2.Lambda.html#5938" class="Function">sucᶜ</a> <a id="29075" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="29077" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a><a id="29082" class="Symbol">))</a>
  <a id="29087" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23261" class="InductiveConstructor Operator">—→⟨</a> <a id="29091" href="plfa.part2.Lambda.html#20312" class="InductiveConstructor">ξ-·₂</a> <a id="29096" href="plfa.part2.Lambda.html#12199" class="InductiveConstructor">V-ƛ</a> <a id="29100" class="Symbol">(</a><a id="29101" href="plfa.part2.Lambda.html#20312" class="InductiveConstructor">ξ-·₂</a> <a id="29106" href="plfa.part2.Lambda.html#12199" class="InductiveConstructor">V-ƛ</a> <a id="29110" class="Symbol">(</a><a id="29111" href="plfa.part2.Lambda.html#20407" class="InductiveConstructor">β-ƛ</a> <a id="29115" href="plfa.part2.Lambda.html#12260" class="InductiveConstructor">V-zero</a><a id="29121" class="Symbol">))</a> <a id="29124" href="plfa.part2.Lambda.html#23261" class="InductiveConstructor Operator">⟩</a>
    <a id="29130" class="Symbol">(</a><a id="29131" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3854" class="InductiveConstructor Operator">ƛ</a> <a id="29133" class="String">&quot;z&quot;</a> <a id="29137" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a> <a id="29139" href="plfa.part2.Lambda.html#5938" class="Function">sucᶜ</a> <a id="29144" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="29146" class="Symbol">(</a><a id="29147" href="plfa.part2.Lambda.html#5938" class="Function">sucᶜ</a> <a id="29152" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="29154" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="29156" class="String">&quot;z&quot;</a><a id="29159" class="Symbol">))</a> <a id="29162" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="29164" class="Symbol">(</a><a id="29165" href="plfa.part2.Lambda.html#5938" class="Function">sucᶜ</a> <a id="29170" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="29172" class="Symbol">(</a><a id="29173" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="29178" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a><a id="29183" class="Symbol">))</a>
  <a id="29188" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23261" class="InductiveConstructor Operator">—→⟨</a> <a id="29192" href="plfa.part2.Lambda.html#20312" class="InductiveConstructor">ξ-·₂</a> <a id="29197" href="plfa.part2.Lambda.html#12199" class="InductiveConstructor">V-ƛ</a> <a id="29201" class="Symbol">(</a><a id="29202" href="plfa.part2.Lambda.html#20407" class="InductiveConstructor">β-ƛ</a> <a id="29206" class="Symbol">(</a><a id="29207" href="plfa.part2.Lambda.html#12308" class="InductiveConstructor">V-suc</a> <a id="29213" href="plfa.part2.Lambda.html#12260" class="InductiveConstructor">V-zero</a><a id="29219" class="Symbol">))</a> <a id="29222" href="plfa.part2.Lambda.html#23261" class="InductiveConstructor Operator">⟩</a>
    <a id="29228" class="Symbol">(</a><a id="29229" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3854" class="InductiveConstructor Operator">ƛ</a> <a id="29231" class="String">&quot;z&quot;</a> <a id="29235" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a> <a id="29237" href="plfa.part2.Lambda.html#5938" class="Function">sucᶜ</a> <a id="29242" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="29244" class="Symbol">(</a><a id="29245" href="plfa.part2.Lambda.html#5938" class="Function">sucᶜ</a> <a id="29250" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="29252" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="29254" class="String">&quot;z&quot;</a><a id="29257" class="Symbol">))</a> <a id="29260" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="29262" class="Symbol">(</a><a id="29263" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="29268" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="29273" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a><a id="29278" class="Symbol">)</a>
  <a id="29282" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23261" class="InductiveConstructor Operator">—→⟨</a> <a id="29286" href="plfa.part2.Lambda.html#20407" class="InductiveConstructor">β-ƛ</a> <a id="29290" class="Symbol">(</a><a id="29291" href="plfa.part2.Lambda.html#12308" class="InductiveConstructor">V-suc</a> <a id="29297" class="Symbol">(</a><a id="29298" href="plfa.part2.Lambda.html#12308" class="InductiveConstructor">V-suc</a> <a id="29304" href="plfa.part2.Lambda.html#12260" class="InductiveConstructor">V-zero</a><a id="29310" class="Symbol">))</a> <a id="29313" href="plfa.part2.Lambda.html#23261" class="InductiveConstructor Operator">⟩</a>
    <a id="29319" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#5938" class="Function">sucᶜ</a> <a id="29324" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="29326" class="Symbol">(</a><a id="29327" href="plfa.part2.Lambda.html#5938" class="Function">sucᶜ</a> <a id="29332" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="29334" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="29339" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="29344" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a><a id="29349" class="Symbol">)</a>
  <a id="29353" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23261" class="InductiveConstructor Operator">—→⟨</a> <a id="29357" href="plfa.part2.Lambda.html#20312" class="InductiveConstructor">ξ-·₂</a> <a id="29362" href="plfa.part2.Lambda.html#12199" class="InductiveConstructor">V-ƛ</a> <a id="29366" class="Symbol">(</a><a id="29367" href="plfa.part2.Lambda.html#20407" class="InductiveConstructor">β-ƛ</a> <a id="29371" class="Symbol">(</a><a id="29372" href="plfa.part2.Lambda.html#12308" class="InductiveConstructor">V-suc</a> <a id="29378" class="Symbol">(</a><a id="29379" href="plfa.part2.Lambda.html#12308" class="InductiveConstructor">V-suc</a> <a id="29385" href="plfa.part2.Lambda.html#12260" class="InductiveConstructor">V-zero</a><a id="29391" class="Symbol">)))</a> <a id="29395" href="plfa.part2.Lambda.html#23261" class="InductiveConstructor Operator">⟩</a>
    <a id="29401" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#5938" class="Function">sucᶜ</a> <a id="29406" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="29408" class="Symbol">(</a><a id="29409" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="29414" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="29419" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="29424" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a><a id="29429" class="Symbol">)</a>
  <a id="29433" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23261" class="InductiveConstructor Operator">—→⟨</a> <a id="29437" href="plfa.part2.Lambda.html#20407" class="InductiveConstructor">β-ƛ</a> <a id="29441" class="Symbol">(</a><a id="29442" href="plfa.part2.Lambda.html#12308" class="InductiveConstructor">V-suc</a> <a id="29448" class="Symbol">(</a><a id="29449" href="plfa.part2.Lambda.html#12308" class="InductiveConstructor">V-suc</a> <a id="29455" class="Symbol">(</a><a id="29456" href="plfa.part2.Lambda.html#12308" class="InductiveConstructor">V-suc</a> <a id="29462" href="plfa.part2.Lambda.html#12260" class="InductiveConstructor">V-zero</a><a id="29468" class="Symbol">)))</a> <a id="29472" href="plfa.part2.Lambda.html#23261" class="InductiveConstructor Operator">⟩</a>
   <a id="29477" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#3982" class="InductiveConstructor Operator">`suc</a> <a id="29482" class="Symbol">(</a><a id="29483" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="29488" class="Symbol">(</a><a id="29489" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="29494" class="Symbol">(</a><a id="29495" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="29500" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a><a id="29505" class="Symbol">)))</a>
  <a id="29511" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#23220" class="InductiveConstructor Operator">∎</a>
</pre>{% endraw %}
In the next chapter, we will see how to compute such reduction sequences.


#### Exercise `plus-example` (practice)

Write out the reduction sequence demonstrating that one plus one is two.

{% raw %}<pre class="Agda"><a id="29713" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}

## Syntax of types

We have just two types:

  * Functions, `A ⇒ B`
  * Naturals, `` `ℕ ``

As before, to avoid overlap we use variants of the names used by Agda.

Here is the syntax of types in BNF:

    A, B, C  ::=  A ⇒ B | `ℕ

And here it is formalised in Agda:

{% raw %}<pre class="Agda"><a id="30013" class="Keyword">infixr</a> <a id="30020" class="Number">7</a> <a id="30022" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#30051" class="InductiveConstructor Operator">_⇒_</a>

<a id="30027" class="Keyword">data</a> <a id="Type"></a><a id="30032" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#30032" class="Datatype">Type</a> <a id="30037" class="Symbol">:</a> <a id="30039" class="PrimitiveType">Set</a> <a id="30043" class="Keyword">where</a>
  <a id="Type._⇒_"></a><a id="30051" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#30051" class="InductiveConstructor Operator">_⇒_</a> <a id="30055" class="Symbol">:</a> <a id="30057" href="plfa.part2.Lambda.html#30032" class="Datatype">Type</a> <a id="30062" class="Symbol">→</a> <a id="30064" href="plfa.part2.Lambda.html#30032" class="Datatype">Type</a> <a id="30069" class="Symbol">→</a> <a id="30071" href="plfa.part2.Lambda.html#30032" class="Datatype">Type</a>
  <a id="Type.`ℕ"></a><a id="30078" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#30078" class="InductiveConstructor">`ℕ</a> <a id="30081" class="Symbol">:</a> <a id="30083" href="plfa.part2.Lambda.html#30032" class="Datatype">Type</a>
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

{% raw %}<pre class="Agda"><a id="31668" class="Keyword">infixl</a> <a id="31675" class="Number">5</a>  <a id="31678" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#31730" class="InductiveConstructor Operator">_,_⦂_</a>

<a id="31685" class="Keyword">data</a> <a id="Context"></a><a id="31690" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#31690" class="Datatype">Context</a> <a id="31698" class="Symbol">:</a> <a id="31700" class="PrimitiveType">Set</a> <a id="31704" class="Keyword">where</a>
  <a id="Context.∅"></a><a id="31712" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#31712" class="InductiveConstructor">∅</a>     <a id="31718" class="Symbol">:</a> <a id="31720" href="plfa.part2.Lambda.html#31690" class="Datatype">Context</a>
  <a id="Context._,_⦂_"></a><a id="31730" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#31730" class="InductiveConstructor Operator">_,_⦂_</a> <a id="31736" class="Symbol">:</a> <a id="31738" href="plfa.part2.Lambda.html#31690" class="Datatype">Context</a> <a id="31746" class="Symbol">→</a> <a id="31748" href="plfa.part2.Lambda.html#3695" class="Function">Id</a> <a id="31751" class="Symbol">→</a> <a id="31753" href="plfa.part2.Lambda.html#30032" class="Datatype">Type</a> <a id="31758" class="Symbol">→</a> <a id="31760" href="plfa.part2.Lambda.html#31690" class="Datatype">Context</a>
</pre>{% endraw %}

#### Exercise `Context-≃` (practice)

Show that `Context` is isomorphic to `List (Id × Type)`.
For instance, the isomorphism relates the context

    ∅ , "s" ⦂ `ℕ ⇒ `ℕ , "z" ⦂ `ℕ

to the list

    [ ⟨ "z" , `ℕ ⟩ , ⟨ "s" , `ℕ ⇒ `ℕ ⟩ ]

{% raw %}<pre class="Agda"><a id="32013" class="Comment">-- Your code goes here</a>
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
{% raw %}<pre class="Agda"><a id="32902" class="Keyword">infix</a>  <a id="32909" class="Number">4</a>  <a id="32912" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#32924" class="Datatype Operator">_∋_⦂_</a>

<a id="32919" class="Keyword">data</a> <a id="_∋_⦂_"></a><a id="32924" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#32924" class="Datatype Operator">_∋_⦂_</a> <a id="32930" class="Symbol">:</a> <a id="32932" href="plfa.part2.Lambda.html#31690" class="Datatype">Context</a> <a id="32940" class="Symbol">→</a> <a id="32942" href="plfa.part2.Lambda.html#3695" class="Function">Id</a> <a id="32945" class="Symbol">→</a> <a id="32947" href="plfa.part2.Lambda.html#30032" class="Datatype">Type</a> <a id="32952" class="Symbol">→</a> <a id="32954" class="PrimitiveType">Set</a> <a id="32958" class="Keyword">where</a>

  <a id="_∋_⦂_.Z"></a><a id="32967" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#32967" class="InductiveConstructor">Z</a> <a id="32969" class="Symbol">:</a> <a id="32971" class="Symbol">∀</a> <a id="32973" class="Symbol">{</a><a id="32974" href="plfa.part2.Lambda.html#32974" class="Bound">Γ</a> <a id="32976" href="plfa.part2.Lambda.html#32976" class="Bound">x</a> <a id="32978" href="plfa.part2.Lambda.html#32978" class="Bound">A</a><a id="32979" class="Symbol">}</a>
      <a id="32987" class="Comment">------------------</a>
    <a id="33010" class="Symbol">→</a> <a id="33012" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#32974" class="Bound">Γ</a> <a id="33014" href="plfa.part2.Lambda.html#31730" class="InductiveConstructor Operator">,</a> <a id="33016" href="plfa.part2.Lambda.html#32976" class="Bound">x</a> <a id="33018" href="plfa.part2.Lambda.html#31730" class="InductiveConstructor Operator">⦂</a> <a id="33020" href="plfa.part2.Lambda.html#32978" class="Bound">A</a> <a id="33022" href="plfa.part2.Lambda.html#32924" class="Datatype Operator">∋</a> <a id="33024" href="plfa.part2.Lambda.html#32976" class="Bound">x</a> <a id="33026" href="plfa.part2.Lambda.html#32924" class="Datatype Operator">⦂</a> <a id="33028" href="plfa.part2.Lambda.html#32978" class="Bound">A</a>

  <a id="_∋_⦂_.S"></a><a id="33033" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#33033" class="InductiveConstructor">S</a> <a id="33035" class="Symbol">:</a> <a id="33037" class="Symbol">∀</a> <a id="33039" class="Symbol">{</a><a id="33040" href="plfa.part2.Lambda.html#33040" class="Bound">Γ</a> <a id="33042" href="plfa.part2.Lambda.html#33042" class="Bound">x</a> <a id="33044" href="plfa.part2.Lambda.html#33044" class="Bound">y</a> <a id="33046" href="plfa.part2.Lambda.html#33046" class="Bound">A</a> <a id="33048" href="plfa.part2.Lambda.html#33048" class="Bound">B</a><a id="33049" class="Symbol">}</a>
    <a id="33055" class="Symbol">→</a> <a id="33057" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#33042" class="Bound">x</a> <a id="33059" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#799" class="Function Operator">≢</a> <a id="33061" href="plfa.part2.Lambda.html#33044" class="Bound">y</a>
    <a id="33067" class="Symbol">→</a> <a id="33069" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#33040" class="Bound">Γ</a> <a id="33071" href="plfa.part2.Lambda.html#32924" class="Datatype Operator">∋</a> <a id="33073" href="plfa.part2.Lambda.html#33042" class="Bound">x</a> <a id="33075" href="plfa.part2.Lambda.html#32924" class="Datatype Operator">⦂</a> <a id="33077" href="plfa.part2.Lambda.html#33046" class="Bound">A</a>
      <a id="33085" class="Comment">------------------</a>
    <a id="33108" class="Symbol">→</a> <a id="33110" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#33040" class="Bound">Γ</a> <a id="33112" href="plfa.part2.Lambda.html#31730" class="InductiveConstructor Operator">,</a> <a id="33114" href="plfa.part2.Lambda.html#33044" class="Bound">y</a> <a id="33116" href="plfa.part2.Lambda.html#31730" class="InductiveConstructor Operator">⦂</a> <a id="33118" href="plfa.part2.Lambda.html#33048" class="Bound">B</a> <a id="33120" href="plfa.part2.Lambda.html#32924" class="Datatype Operator">∋</a> <a id="33122" href="plfa.part2.Lambda.html#33042" class="Bound">x</a> <a id="33124" href="plfa.part2.Lambda.html#32924" class="Datatype Operator">⦂</a> <a id="33126" href="plfa.part2.Lambda.html#33046" class="Bound">A</a>
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
{% raw %}<pre class="Agda"><a id="34066" class="Keyword">infix</a>  <a id="34073" class="Number">4</a>  <a id="34076" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#34088" class="Datatype Operator">_⊢_⦂_</a>

<a id="34083" class="Keyword">data</a> <a id="_⊢_⦂_"></a><a id="34088" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#34088" class="Datatype Operator">_⊢_⦂_</a> <a id="34094" class="Symbol">:</a> <a id="34096" href="plfa.part2.Lambda.html#31690" class="Datatype">Context</a> <a id="34104" class="Symbol">→</a> <a id="34106" href="plfa.part2.Lambda.html#3796" class="Datatype">Term</a> <a id="34111" class="Symbol">→</a> <a id="34113" href="plfa.part2.Lambda.html#30032" class="Datatype">Type</a> <a id="34118" class="Symbol">→</a> <a id="34120" class="PrimitiveType">Set</a> <a id="34124" class="Keyword">where</a>

  <a id="34133" class="Comment">-- Axiom </a>
  <a id="_⊢_⦂_.⊢`"></a><a id="34145" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#34145" class="InductiveConstructor">⊢`</a> <a id="34148" class="Symbol">:</a> <a id="34150" class="Symbol">∀</a> <a id="34152" class="Symbol">{</a><a id="34153" href="plfa.part2.Lambda.html#34153" class="Bound">Γ</a> <a id="34155" href="plfa.part2.Lambda.html#34155" class="Bound">x</a> <a id="34157" href="plfa.part2.Lambda.html#34157" class="Bound">A</a><a id="34158" class="Symbol">}</a>
    <a id="34164" class="Symbol">→</a> <a id="34166" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#34153" class="Bound">Γ</a> <a id="34168" href="plfa.part2.Lambda.html#32924" class="Datatype Operator">∋</a> <a id="34170" href="plfa.part2.Lambda.html#34155" class="Bound">x</a> <a id="34172" href="plfa.part2.Lambda.html#32924" class="Datatype Operator">⦂</a> <a id="34174" href="plfa.part2.Lambda.html#34157" class="Bound">A</a>
      <a id="34182" class="Comment">-----------</a>
    <a id="34198" class="Symbol">→</a> <a id="34200" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#34153" class="Bound">Γ</a> <a id="34202" href="plfa.part2.Lambda.html#34088" class="Datatype Operator">⊢</a> <a id="34204" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="34206" href="plfa.part2.Lambda.html#34155" class="Bound">x</a> <a id="34208" href="plfa.part2.Lambda.html#34088" class="Datatype Operator">⦂</a> <a id="34210" href="plfa.part2.Lambda.html#34157" class="Bound">A</a>

  <a id="34215" class="Comment">-- ⇒-I </a>
  <a id="_⊢_⦂_.⊢ƛ"></a><a id="34225" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#34225" class="InductiveConstructor">⊢ƛ</a> <a id="34228" class="Symbol">:</a> <a id="34230" class="Symbol">∀</a> <a id="34232" class="Symbol">{</a><a id="34233" href="plfa.part2.Lambda.html#34233" class="Bound">Γ</a> <a id="34235" href="plfa.part2.Lambda.html#34235" class="Bound">x</a> <a id="34237" href="plfa.part2.Lambda.html#34237" class="Bound">N</a> <a id="34239" href="plfa.part2.Lambda.html#34239" class="Bound">A</a> <a id="34241" href="plfa.part2.Lambda.html#34241" class="Bound">B</a><a id="34242" class="Symbol">}</a>
    <a id="34248" class="Symbol">→</a> <a id="34250" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#34233" class="Bound">Γ</a> <a id="34252" href="plfa.part2.Lambda.html#31730" class="InductiveConstructor Operator">,</a> <a id="34254" href="plfa.part2.Lambda.html#34235" class="Bound">x</a> <a id="34256" href="plfa.part2.Lambda.html#31730" class="InductiveConstructor Operator">⦂</a> <a id="34258" href="plfa.part2.Lambda.html#34239" class="Bound">A</a> <a id="34260" href="plfa.part2.Lambda.html#34088" class="Datatype Operator">⊢</a> <a id="34262" href="plfa.part2.Lambda.html#34237" class="Bound">N</a> <a id="34264" href="plfa.part2.Lambda.html#34088" class="Datatype Operator">⦂</a> <a id="34266" href="plfa.part2.Lambda.html#34241" class="Bound">B</a>
      <a id="34274" class="Comment">-------------------</a>
    <a id="34298" class="Symbol">→</a> <a id="34300" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#34233" class="Bound">Γ</a> <a id="34302" href="plfa.part2.Lambda.html#34088" class="Datatype Operator">⊢</a> <a id="34304" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">ƛ</a> <a id="34306" href="plfa.part2.Lambda.html#34235" class="Bound">x</a> <a id="34308" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a> <a id="34310" href="plfa.part2.Lambda.html#34237" class="Bound">N</a> <a id="34312" href="plfa.part2.Lambda.html#34088" class="Datatype Operator">⦂</a> <a id="34314" href="plfa.part2.Lambda.html#34239" class="Bound">A</a> <a id="34316" href="plfa.part2.Lambda.html#30051" class="InductiveConstructor Operator">⇒</a> <a id="34318" href="plfa.part2.Lambda.html#34241" class="Bound">B</a>

  <a id="34323" class="Comment">-- ⇒-E</a>
  <a id="_⊢_⦂_._·_"></a><a id="34332" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#34332" class="InductiveConstructor Operator">_·_</a> <a id="34336" class="Symbol">:</a> <a id="34338" class="Symbol">∀</a> <a id="34340" class="Symbol">{</a><a id="34341" href="plfa.part2.Lambda.html#34341" class="Bound">Γ</a> <a id="34343" href="plfa.part2.Lambda.html#34343" class="Bound">L</a> <a id="34345" href="plfa.part2.Lambda.html#34345" class="Bound">M</a> <a id="34347" href="plfa.part2.Lambda.html#34347" class="Bound">A</a> <a id="34349" href="plfa.part2.Lambda.html#34349" class="Bound">B</a><a id="34350" class="Symbol">}</a>
    <a id="34356" class="Symbol">→</a> <a id="34358" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#34341" class="Bound">Γ</a> <a id="34360" href="plfa.part2.Lambda.html#34088" class="Datatype Operator">⊢</a> <a id="34362" href="plfa.part2.Lambda.html#34343" class="Bound">L</a> <a id="34364" href="plfa.part2.Lambda.html#34088" class="Datatype Operator">⦂</a> <a id="34366" href="plfa.part2.Lambda.html#34347" class="Bound">A</a> <a id="34368" href="plfa.part2.Lambda.html#30051" class="InductiveConstructor Operator">⇒</a> <a id="34370" href="plfa.part2.Lambda.html#34349" class="Bound">B</a>
    <a id="34376" class="Symbol">→</a> <a id="34378" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#34341" class="Bound">Γ</a> <a id="34380" href="plfa.part2.Lambda.html#34088" class="Datatype Operator">⊢</a> <a id="34382" href="plfa.part2.Lambda.html#34345" class="Bound">M</a> <a id="34384" href="plfa.part2.Lambda.html#34088" class="Datatype Operator">⦂</a> <a id="34386" href="plfa.part2.Lambda.html#34347" class="Bound">A</a>
      <a id="34394" class="Comment">-------------</a>
    <a id="34412" class="Symbol">→</a> <a id="34414" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#34341" class="Bound">Γ</a> <a id="34416" href="plfa.part2.Lambda.html#34088" class="Datatype Operator">⊢</a> <a id="34418" href="plfa.part2.Lambda.html#34343" class="Bound">L</a> <a id="34420" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="34422" href="plfa.part2.Lambda.html#34345" class="Bound">M</a> <a id="34424" href="plfa.part2.Lambda.html#34088" class="Datatype Operator">⦂</a> <a id="34426" href="plfa.part2.Lambda.html#34349" class="Bound">B</a>

  <a id="34431" class="Comment">-- ℕ-I₁</a>
  <a id="_⊢_⦂_.⊢zero"></a><a id="34441" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#34441" class="InductiveConstructor">⊢zero</a> <a id="34447" class="Symbol">:</a> <a id="34449" class="Symbol">∀</a> <a id="34451" class="Symbol">{</a><a id="34452" href="plfa.part2.Lambda.html#34452" class="Bound">Γ</a><a id="34453" class="Symbol">}</a>
      <a id="34461" class="Comment">--------------</a>
    <a id="34480" class="Symbol">→</a> <a id="34482" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#34452" class="Bound">Γ</a> <a id="34484" href="plfa.part2.Lambda.html#34088" class="Datatype Operator">⊢</a> <a id="34486" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a> <a id="34492" href="plfa.part2.Lambda.html#34088" class="Datatype Operator">⦂</a> <a id="34494" href="plfa.part2.Lambda.html#30078" class="InductiveConstructor">`ℕ</a>

  <a id="34500" class="Comment">-- ℕ-I₂</a>
  <a id="_⊢_⦂_.⊢suc"></a><a id="34510" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#34510" class="InductiveConstructor">⊢suc</a> <a id="34515" class="Symbol">:</a> <a id="34517" class="Symbol">∀</a> <a id="34519" class="Symbol">{</a><a id="34520" href="plfa.part2.Lambda.html#34520" class="Bound">Γ</a> <a id="34522" href="plfa.part2.Lambda.html#34522" class="Bound">M</a><a id="34523" class="Symbol">}</a>
    <a id="34529" class="Symbol">→</a> <a id="34531" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#34520" class="Bound">Γ</a> <a id="34533" href="plfa.part2.Lambda.html#34088" class="Datatype Operator">⊢</a> <a id="34535" href="plfa.part2.Lambda.html#34522" class="Bound">M</a> <a id="34537" href="plfa.part2.Lambda.html#34088" class="Datatype Operator">⦂</a> <a id="34539" href="plfa.part2.Lambda.html#30078" class="InductiveConstructor">`ℕ</a>
      <a id="34548" class="Comment">---------------</a>
    <a id="34568" class="Symbol">→</a> <a id="34570" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#34520" class="Bound">Γ</a> <a id="34572" href="plfa.part2.Lambda.html#34088" class="Datatype Operator">⊢</a> <a id="34574" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="34579" href="plfa.part2.Lambda.html#34522" class="Bound">M</a> <a id="34581" href="plfa.part2.Lambda.html#34088" class="Datatype Operator">⦂</a> <a id="34583" href="plfa.part2.Lambda.html#30078" class="InductiveConstructor">`ℕ</a>

  <a id="34589" class="Comment">-- ℕ-E</a>
  <a id="_⊢_⦂_.⊢case"></a><a id="34598" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#34598" class="InductiveConstructor">⊢case</a> <a id="34604" class="Symbol">:</a> <a id="34606" class="Symbol">∀</a> <a id="34608" class="Symbol">{</a><a id="34609" href="plfa.part2.Lambda.html#34609" class="Bound">Γ</a> <a id="34611" href="plfa.part2.Lambda.html#34611" class="Bound">L</a> <a id="34613" href="plfa.part2.Lambda.html#34613" class="Bound">M</a> <a id="34615" href="plfa.part2.Lambda.html#34615" class="Bound">x</a> <a id="34617" href="plfa.part2.Lambda.html#34617" class="Bound">N</a> <a id="34619" href="plfa.part2.Lambda.html#34619" class="Bound">A</a><a id="34620" class="Symbol">}</a>
    <a id="34626" class="Symbol">→</a> <a id="34628" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#34609" class="Bound">Γ</a> <a id="34630" href="plfa.part2.Lambda.html#34088" class="Datatype Operator">⊢</a> <a id="34632" href="plfa.part2.Lambda.html#34611" class="Bound">L</a> <a id="34634" href="plfa.part2.Lambda.html#34088" class="Datatype Operator">⦂</a> <a id="34636" href="plfa.part2.Lambda.html#30078" class="InductiveConstructor">`ℕ</a>
    <a id="34643" class="Symbol">→</a> <a id="34645" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#34609" class="Bound">Γ</a> <a id="34647" href="plfa.part2.Lambda.html#34088" class="Datatype Operator">⊢</a> <a id="34649" href="plfa.part2.Lambda.html#34613" class="Bound">M</a> <a id="34651" href="plfa.part2.Lambda.html#34088" class="Datatype Operator">⦂</a> <a id="34653" href="plfa.part2.Lambda.html#34619" class="Bound">A</a>
    <a id="34659" class="Symbol">→</a> <a id="34661" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#34609" class="Bound">Γ</a> <a id="34663" href="plfa.part2.Lambda.html#31730" class="InductiveConstructor Operator">,</a> <a id="34665" href="plfa.part2.Lambda.html#34615" class="Bound">x</a> <a id="34667" href="plfa.part2.Lambda.html#31730" class="InductiveConstructor Operator">⦂</a> <a id="34669" href="plfa.part2.Lambda.html#30078" class="InductiveConstructor">`ℕ</a> <a id="34672" href="plfa.part2.Lambda.html#34088" class="Datatype Operator">⊢</a> <a id="34674" href="plfa.part2.Lambda.html#34617" class="Bound">N</a> <a id="34676" href="plfa.part2.Lambda.html#34088" class="Datatype Operator">⦂</a> <a id="34678" href="plfa.part2.Lambda.html#34619" class="Bound">A</a>
      <a id="34686" class="Comment">-------------------------------------</a>
    <a id="34728" class="Symbol">→</a> <a id="34730" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#34609" class="Bound">Γ</a> <a id="34732" href="plfa.part2.Lambda.html#34088" class="Datatype Operator">⊢</a> <a id="34734" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">case</a> <a id="34739" href="plfa.part2.Lambda.html#34611" class="Bound">L</a> <a id="34741" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">[zero⇒</a> <a id="34748" href="plfa.part2.Lambda.html#34613" class="Bound">M</a> <a id="34750" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">|suc</a> <a id="34755" href="plfa.part2.Lambda.html#34615" class="Bound">x</a> <a id="34757" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">⇒</a> <a id="34759" href="plfa.part2.Lambda.html#34617" class="Bound">N</a> <a id="34761" href="plfa.part2.Lambda.html#4023" class="InductiveConstructor Operator">]</a> <a id="34763" href="plfa.part2.Lambda.html#34088" class="Datatype Operator">⦂</a> <a id="34765" href="plfa.part2.Lambda.html#34619" class="Bound">A</a>

  <a id="_⊢_⦂_.⊢μ"></a><a id="34770" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#34770" class="InductiveConstructor">⊢μ</a> <a id="34773" class="Symbol">:</a> <a id="34775" class="Symbol">∀</a> <a id="34777" class="Symbol">{</a><a id="34778" href="plfa.part2.Lambda.html#34778" class="Bound">Γ</a> <a id="34780" href="plfa.part2.Lambda.html#34780" class="Bound">x</a> <a id="34782" href="plfa.part2.Lambda.html#34782" class="Bound">M</a> <a id="34784" href="plfa.part2.Lambda.html#34784" class="Bound">A</a><a id="34785" class="Symbol">}</a>
    <a id="34791" class="Symbol">→</a> <a id="34793" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#34778" class="Bound">Γ</a> <a id="34795" href="plfa.part2.Lambda.html#31730" class="InductiveConstructor Operator">,</a> <a id="34797" href="plfa.part2.Lambda.html#34780" class="Bound">x</a> <a id="34799" href="plfa.part2.Lambda.html#31730" class="InductiveConstructor Operator">⦂</a> <a id="34801" href="plfa.part2.Lambda.html#34784" class="Bound">A</a> <a id="34803" href="plfa.part2.Lambda.html#34088" class="Datatype Operator">⊢</a> <a id="34805" href="plfa.part2.Lambda.html#34782" class="Bound">M</a> <a id="34807" href="plfa.part2.Lambda.html#34088" class="Datatype Operator">⦂</a> <a id="34809" href="plfa.part2.Lambda.html#34784" class="Bound">A</a>
      <a id="34817" class="Comment">-----------------</a>
    <a id="34839" class="Symbol">→</a> <a id="34841" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#34778" class="Bound">Γ</a> <a id="34843" href="plfa.part2.Lambda.html#34088" class="Datatype Operator">⊢</a> <a id="34845" href="plfa.part2.Lambda.html#4083" class="InductiveConstructor Operator">μ</a> <a id="34847" href="plfa.part2.Lambda.html#34780" class="Bound">x</a> <a id="34849" href="plfa.part2.Lambda.html#4083" class="InductiveConstructor Operator">⇒</a> <a id="34851" href="plfa.part2.Lambda.html#34782" class="Bound">M</a> <a id="34853" href="plfa.part2.Lambda.html#34088" class="Datatype Operator">⦂</a> <a id="34855" href="plfa.part2.Lambda.html#34784" class="Bound">A</a>
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
{% raw %}<pre class="Agda"><a id="Ch"></a><a id="37339" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#37339" class="Function">Ch</a> <a id="37342" class="Symbol">:</a> <a id="37344" href="plfa.part2.Lambda.html#30032" class="Datatype">Type</a> <a id="37349" class="Symbol">→</a> <a id="37351" href="plfa.part2.Lambda.html#30032" class="Datatype">Type</a>
<a id="37356" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#37339" class="Function">Ch</a> <a id="37359" href="plfa.part2.Lambda.html#37359" class="Bound">A</a> <a id="37361" class="Symbol">=</a> <a id="37363" class="Symbol">(</a><a id="37364" href="plfa.part2.Lambda.html#37359" class="Bound">A</a> <a id="37366" href="plfa.part2.Lambda.html#30051" class="InductiveConstructor Operator">⇒</a> <a id="37368" href="plfa.part2.Lambda.html#37359" class="Bound">A</a><a id="37369" class="Symbol">)</a> <a id="37371" href="plfa.part2.Lambda.html#30051" class="InductiveConstructor Operator">⇒</a> <a id="37373" href="plfa.part2.Lambda.html#37359" class="Bound">A</a> <a id="37375" href="plfa.part2.Lambda.html#30051" class="InductiveConstructor Operator">⇒</a> <a id="37377" href="plfa.part2.Lambda.html#37359" class="Bound">A</a>

<a id="⊢twoᶜ"></a><a id="37380" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#37380" class="Function">⊢twoᶜ</a> <a id="37386" class="Symbol">:</a> <a id="37388" class="Symbol">∀</a> <a id="37390" class="Symbol">{</a><a id="37391" href="plfa.part2.Lambda.html#37391" class="Bound">Γ</a> <a id="37393" href="plfa.part2.Lambda.html#37393" class="Bound">A</a><a id="37394" class="Symbol">}</a> <a id="37396" class="Symbol">→</a> <a id="37398" href="plfa.part2.Lambda.html#37391" class="Bound">Γ</a> <a id="37400" href="plfa.part2.Lambda.html#34088" class="Datatype Operator">⊢</a> <a id="37402" href="plfa.part2.Lambda.html#5773" class="Function">twoᶜ</a> <a id="37407" href="plfa.part2.Lambda.html#34088" class="Datatype Operator">⦂</a> <a id="37409" href="plfa.part2.Lambda.html#37339" class="Function">Ch</a> <a id="37412" href="plfa.part2.Lambda.html#37393" class="Bound">A</a>
<a id="37414" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#37380" class="Function">⊢twoᶜ</a> <a id="37420" class="Symbol">=</a> <a id="37422" href="plfa.part2.Lambda.html#34225" class="InductiveConstructor">⊢ƛ</a> <a id="37425" class="Symbol">(</a><a id="37426" href="plfa.part2.Lambda.html#34225" class="InductiveConstructor">⊢ƛ</a> <a id="37429" class="Symbol">(</a><a id="37430" href="plfa.part2.Lambda.html#34145" class="InductiveConstructor">⊢`</a> <a id="37433" href="plfa.part2.Lambda.html#37466" class="Function">∋s</a> <a id="37436" href="plfa.part2.Lambda.html#34332" class="InductiveConstructor Operator">·</a> <a id="37438" class="Symbol">(</a><a id="37439" href="plfa.part2.Lambda.html#34145" class="InductiveConstructor">⊢`</a> <a id="37442" href="plfa.part2.Lambda.html#37466" class="Function">∋s</a> <a id="37445" href="plfa.part2.Lambda.html#34332" class="InductiveConstructor Operator">·</a> <a id="37447" href="plfa.part2.Lambda.html#34145" class="InductiveConstructor">⊢`</a> <a id="37450" href="plfa.part2.Lambda.html#37483" class="Function">∋z</a><a id="37452" class="Symbol">)))</a>
  <a id="37458" class="Keyword">where</a>
  <a id="37466" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#37466" class="Function">∋s</a> <a id="37469" class="Symbol">=</a> <a id="37471" href="plfa.part2.Lambda.html#33033" class="InductiveConstructor">S</a> <a id="37473" class="Symbol">(λ())</a> <a id="37479" href="plfa.part2.Lambda.html#32967" class="InductiveConstructor">Z</a>
  <a id="37483" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#37483" class="Function">∋z</a> <a id="37486" class="Symbol">=</a> <a id="37488" href="plfa.part2.Lambda.html#32967" class="InductiveConstructor">Z</a>
</pre>{% endraw %}
Here are the typings corresponding to computing two plus two:
{% raw %}<pre class="Agda"><a id="⊢two"></a><a id="37561" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#37561" class="Function">⊢two</a> <a id="37566" class="Symbol">:</a> <a id="37568" class="Symbol">∀</a> <a id="37570" class="Symbol">{</a><a id="37571" href="plfa.part2.Lambda.html#37571" class="Bound">Γ</a><a id="37572" class="Symbol">}</a> <a id="37574" class="Symbol">→</a> <a id="37576" href="plfa.part2.Lambda.html#37571" class="Bound">Γ</a> <a id="37578" href="plfa.part2.Lambda.html#34088" class="Datatype Operator">⊢</a> <a id="37580" href="plfa.part2.Lambda.html#4524" class="Function">two</a> <a id="37584" href="plfa.part2.Lambda.html#34088" class="Datatype Operator">⦂</a> <a id="37586" href="plfa.part2.Lambda.html#30078" class="InductiveConstructor">`ℕ</a>
<a id="37589" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#37561" class="Function">⊢two</a> <a id="37594" class="Symbol">=</a> <a id="37596" href="plfa.part2.Lambda.html#34510" class="InductiveConstructor">⊢suc</a> <a id="37601" class="Symbol">(</a><a id="37602" href="plfa.part2.Lambda.html#34510" class="InductiveConstructor">⊢suc</a> <a id="37607" href="plfa.part2.Lambda.html#34441" class="InductiveConstructor">⊢zero</a><a id="37612" class="Symbol">)</a>

<a id="⊢plus"></a><a id="37615" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#37615" class="Function">⊢plus</a> <a id="37621" class="Symbol">:</a> <a id="37623" class="Symbol">∀</a> <a id="37625" class="Symbol">{</a><a id="37626" href="plfa.part2.Lambda.html#37626" class="Bound">Γ</a><a id="37627" class="Symbol">}</a> <a id="37629" class="Symbol">→</a> <a id="37631" href="plfa.part2.Lambda.html#37626" class="Bound">Γ</a> <a id="37633" href="plfa.part2.Lambda.html#34088" class="Datatype Operator">⊢</a> <a id="37635" href="plfa.part2.Lambda.html#4558" class="Function">plus</a> <a id="37640" href="plfa.part2.Lambda.html#34088" class="Datatype Operator">⦂</a> <a id="37642" href="plfa.part2.Lambda.html#30078" class="InductiveConstructor">`ℕ</a> <a id="37645" href="plfa.part2.Lambda.html#30051" class="InductiveConstructor Operator">⇒</a> <a id="37647" href="plfa.part2.Lambda.html#30078" class="InductiveConstructor">`ℕ</a> <a id="37650" href="plfa.part2.Lambda.html#30051" class="InductiveConstructor Operator">⇒</a> <a id="37652" href="plfa.part2.Lambda.html#30078" class="InductiveConstructor">`ℕ</a>
<a id="37655" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#37615" class="Function">⊢plus</a> <a id="37661" class="Symbol">=</a> <a id="37663" href="plfa.part2.Lambda.html#34770" class="InductiveConstructor">⊢μ</a> <a id="37666" class="Symbol">(</a><a id="37667" href="plfa.part2.Lambda.html#34225" class="InductiveConstructor">⊢ƛ</a> <a id="37670" class="Symbol">(</a><a id="37671" href="plfa.part2.Lambda.html#34225" class="InductiveConstructor">⊢ƛ</a> <a id="37674" class="Symbol">(</a><a id="37675" href="plfa.part2.Lambda.html#34598" class="InductiveConstructor">⊢case</a> <a id="37681" class="Symbol">(</a><a id="37682" href="plfa.part2.Lambda.html#34145" class="InductiveConstructor">⊢`</a> <a id="37685" href="plfa.part2.Lambda.html#37792" class="Function">∋m</a><a id="37687" class="Symbol">)</a> <a id="37689" class="Symbol">(</a><a id="37690" href="plfa.part2.Lambda.html#34145" class="InductiveConstructor">⊢`</a> <a id="37693" href="plfa.part2.Lambda.html#37812" class="Function">∋n</a><a id="37695" class="Symbol">)</a>
         <a id="37706" class="Symbol">(</a><a id="37707" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#34510" class="InductiveConstructor">⊢suc</a> <a id="37712" class="Symbol">(</a><a id="37713" href="plfa.part2.Lambda.html#34145" class="InductiveConstructor">⊢`</a> <a id="37716" href="plfa.part2.Lambda.html#37752" class="Function">∋+</a> <a id="37719" href="plfa.part2.Lambda.html#34332" class="InductiveConstructor Operator">·</a> <a id="37721" href="plfa.part2.Lambda.html#34145" class="InductiveConstructor">⊢`</a> <a id="37724" href="plfa.part2.Lambda.html#37822" class="Function">∋m′</a> <a id="37728" href="plfa.part2.Lambda.html#34332" class="InductiveConstructor Operator">·</a> <a id="37730" href="plfa.part2.Lambda.html#34145" class="InductiveConstructor">⊢`</a> <a id="37733" href="plfa.part2.Lambda.html#37832" class="Function">∋n′</a><a id="37736" class="Symbol">)))))</a>
  <a id="37744" class="Keyword">where</a>
  <a id="37752" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#37752" class="Function">∋+</a>  <a id="37756" class="Symbol">=</a> <a id="37758" class="Symbol">(</a><a id="37759" href="plfa.part2.Lambda.html#33033" class="InductiveConstructor">S</a> <a id="37761" class="Symbol">(λ())</a> <a id="37767" class="Symbol">(</a><a id="37768" href="plfa.part2.Lambda.html#33033" class="InductiveConstructor">S</a> <a id="37770" class="Symbol">(λ())</a> <a id="37776" class="Symbol">(</a><a id="37777" href="plfa.part2.Lambda.html#33033" class="InductiveConstructor">S</a> <a id="37779" class="Symbol">(λ())</a> <a id="37785" href="plfa.part2.Lambda.html#32967" class="InductiveConstructor">Z</a><a id="37786" class="Symbol">)))</a>
  <a id="37792" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#37792" class="Function">∋m</a>  <a id="37796" class="Symbol">=</a> <a id="37798" class="Symbol">(</a><a id="37799" href="plfa.part2.Lambda.html#33033" class="InductiveConstructor">S</a> <a id="37801" class="Symbol">(λ())</a> <a id="37807" href="plfa.part2.Lambda.html#32967" class="InductiveConstructor">Z</a><a id="37808" class="Symbol">)</a>
  <a id="37812" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#37812" class="Function">∋n</a>  <a id="37816" class="Symbol">=</a> <a id="37818" href="plfa.part2.Lambda.html#32967" class="InductiveConstructor">Z</a>
  <a id="37822" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#37822" class="Function">∋m′</a> <a id="37826" class="Symbol">=</a> <a id="37828" href="plfa.part2.Lambda.html#32967" class="InductiveConstructor">Z</a>
  <a id="37832" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#37832" class="Function">∋n′</a> <a id="37836" class="Symbol">=</a> <a id="37838" class="Symbol">(</a><a id="37839" href="plfa.part2.Lambda.html#33033" class="InductiveConstructor">S</a> <a id="37841" class="Symbol">(λ())</a> <a id="37847" href="plfa.part2.Lambda.html#32967" class="InductiveConstructor">Z</a><a id="37848" class="Symbol">)</a>

<a id="⊢2+2"></a><a id="37851" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#37851" class="Function">⊢2+2</a> <a id="37856" class="Symbol">:</a> <a id="37858" href="plfa.part2.Lambda.html#31712" class="InductiveConstructor">∅</a> <a id="37860" href="plfa.part2.Lambda.html#34088" class="Datatype Operator">⊢</a> <a id="37862" href="plfa.part2.Lambda.html#4558" class="Function">plus</a> <a id="37867" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="37869" href="plfa.part2.Lambda.html#4524" class="Function">two</a> <a id="37873" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="37875" href="plfa.part2.Lambda.html#4524" class="Function">two</a> <a id="37879" href="plfa.part2.Lambda.html#34088" class="Datatype Operator">⦂</a> <a id="37881" href="plfa.part2.Lambda.html#30078" class="InductiveConstructor">`ℕ</a>
<a id="37884" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#37851" class="Function">⊢2+2</a> <a id="37889" class="Symbol">=</a> <a id="37891" href="plfa.part2.Lambda.html#37615" class="Function">⊢plus</a> <a id="37897" href="plfa.part2.Lambda.html#34332" class="InductiveConstructor Operator">·</a> <a id="37899" href="plfa.part2.Lambda.html#37561" class="Function">⊢two</a> <a id="37904" href="plfa.part2.Lambda.html#34332" class="InductiveConstructor Operator">·</a> <a id="37906" href="plfa.part2.Lambda.html#37561" class="Function">⊢two</a>
</pre>{% endraw %}In contrast to our earlier examples, here we have typed `two` and `plus`
in an arbitrary context rather than the empty context; this makes it easy
to use them inside other binding contexts as well as at the top level.
Here the two lookup judgments `∋m` and `∋m′` refer to two different
bindings of variables named `"m"`.  In contrast, the two judgments `∋n` and
`∋n′` both refer to the same binding of `"n"` but accessed in different
contexts, the first where "n" is the last binding in the context, and
the second after "m" is bound in the successor branch of the case.

And here are typings for the remainder of the Church example:
{% raw %}<pre class="Agda"><a id="⊢plusᶜ"></a><a id="38553" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#38553" class="Function">⊢plusᶜ</a> <a id="38560" class="Symbol">:</a> <a id="38562" class="Symbol">∀</a> <a id="38564" class="Symbol">{</a><a id="38565" href="plfa.part2.Lambda.html#38565" class="Bound">Γ</a> <a id="38567" href="plfa.part2.Lambda.html#38567" class="Bound">A</a><a id="38568" class="Symbol">}</a> <a id="38570" class="Symbol">→</a> <a id="38572" href="plfa.part2.Lambda.html#38565" class="Bound">Γ</a>  <a id="38575" href="plfa.part2.Lambda.html#34088" class="Datatype Operator">⊢</a> <a id="38577" href="plfa.part2.Lambda.html#5834" class="Function">plusᶜ</a> <a id="38583" href="plfa.part2.Lambda.html#34088" class="Datatype Operator">⦂</a> <a id="38585" href="plfa.part2.Lambda.html#37339" class="Function">Ch</a> <a id="38588" href="plfa.part2.Lambda.html#38567" class="Bound">A</a> <a id="38590" href="plfa.part2.Lambda.html#30051" class="InductiveConstructor Operator">⇒</a> <a id="38592" href="plfa.part2.Lambda.html#37339" class="Function">Ch</a> <a id="38595" href="plfa.part2.Lambda.html#38567" class="Bound">A</a> <a id="38597" href="plfa.part2.Lambda.html#30051" class="InductiveConstructor Operator">⇒</a> <a id="38599" href="plfa.part2.Lambda.html#37339" class="Function">Ch</a> <a id="38602" href="plfa.part2.Lambda.html#38567" class="Bound">A</a>
<a id="38604" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#38553" class="Function">⊢plusᶜ</a> <a id="38611" class="Symbol">=</a> <a id="38613" href="plfa.part2.Lambda.html#34225" class="InductiveConstructor">⊢ƛ</a> <a id="38616" class="Symbol">(</a><a id="38617" href="plfa.part2.Lambda.html#34225" class="InductiveConstructor">⊢ƛ</a> <a id="38620" class="Symbol">(</a><a id="38621" href="plfa.part2.Lambda.html#34225" class="InductiveConstructor">⊢ƛ</a> <a id="38624" class="Symbol">(</a><a id="38625" href="plfa.part2.Lambda.html#34225" class="InductiveConstructor">⊢ƛ</a> <a id="38628" class="Symbol">(</a><a id="38629" href="plfa.part2.Lambda.html#34145" class="InductiveConstructor">⊢`</a> <a id="38632" href="plfa.part2.Lambda.html#38683" class="Function">∋m</a> <a id="38635" href="plfa.part2.Lambda.html#34332" class="InductiveConstructor Operator">·</a> <a id="38637" href="plfa.part2.Lambda.html#34145" class="InductiveConstructor">⊢`</a> <a id="38640" href="plfa.part2.Lambda.html#38747" class="Function">∋s</a> <a id="38643" href="plfa.part2.Lambda.html#34332" class="InductiveConstructor Operator">·</a> <a id="38645" class="Symbol">(</a><a id="38646" href="plfa.part2.Lambda.html#34145" class="InductiveConstructor">⊢`</a> <a id="38649" href="plfa.part2.Lambda.html#38720" class="Function">∋n</a> <a id="38652" href="plfa.part2.Lambda.html#34332" class="InductiveConstructor Operator">·</a> <a id="38654" href="plfa.part2.Lambda.html#34145" class="InductiveConstructor">⊢`</a> <a id="38657" href="plfa.part2.Lambda.html#38747" class="Function">∋s</a> <a id="38660" href="plfa.part2.Lambda.html#34332" class="InductiveConstructor Operator">·</a> <a id="38662" href="plfa.part2.Lambda.html#34145" class="InductiveConstructor">⊢`</a> <a id="38665" href="plfa.part2.Lambda.html#38764" class="Function">∋z</a><a id="38667" class="Symbol">)))))</a>
  <a id="38675" class="Keyword">where</a>
  <a id="38683" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#38683" class="Function">∋m</a> <a id="38686" class="Symbol">=</a> <a id="38688" href="plfa.part2.Lambda.html#33033" class="InductiveConstructor">S</a> <a id="38690" class="Symbol">(λ())</a> <a id="38696" class="Symbol">(</a><a id="38697" href="plfa.part2.Lambda.html#33033" class="InductiveConstructor">S</a> <a id="38699" class="Symbol">(λ())</a> <a id="38705" class="Symbol">(</a><a id="38706" href="plfa.part2.Lambda.html#33033" class="InductiveConstructor">S</a> <a id="38708" class="Symbol">(λ())</a> <a id="38714" href="plfa.part2.Lambda.html#32967" class="InductiveConstructor">Z</a><a id="38715" class="Symbol">))</a>
  <a id="38720" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#38720" class="Function">∋n</a> <a id="38723" class="Symbol">=</a> <a id="38725" href="plfa.part2.Lambda.html#33033" class="InductiveConstructor">S</a> <a id="38727" class="Symbol">(λ())</a> <a id="38733" class="Symbol">(</a><a id="38734" href="plfa.part2.Lambda.html#33033" class="InductiveConstructor">S</a> <a id="38736" class="Symbol">(λ())</a> <a id="38742" href="plfa.part2.Lambda.html#32967" class="InductiveConstructor">Z</a><a id="38743" class="Symbol">)</a>
  <a id="38747" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#38747" class="Function">∋s</a> <a id="38750" class="Symbol">=</a> <a id="38752" href="plfa.part2.Lambda.html#33033" class="InductiveConstructor">S</a> <a id="38754" class="Symbol">(λ())</a> <a id="38760" href="plfa.part2.Lambda.html#32967" class="InductiveConstructor">Z</a>
  <a id="38764" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#38764" class="Function">∋z</a> <a id="38767" class="Symbol">=</a> <a id="38769" href="plfa.part2.Lambda.html#32967" class="InductiveConstructor">Z</a>

<a id="⊢sucᶜ"></a><a id="38772" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#38772" class="Function">⊢sucᶜ</a> <a id="38778" class="Symbol">:</a> <a id="38780" class="Symbol">∀</a> <a id="38782" class="Symbol">{</a><a id="38783" href="plfa.part2.Lambda.html#38783" class="Bound">Γ</a><a id="38784" class="Symbol">}</a> <a id="38786" class="Symbol">→</a> <a id="38788" href="plfa.part2.Lambda.html#38783" class="Bound">Γ</a> <a id="38790" href="plfa.part2.Lambda.html#34088" class="Datatype Operator">⊢</a> <a id="38792" href="plfa.part2.Lambda.html#5938" class="Function">sucᶜ</a> <a id="38797" href="plfa.part2.Lambda.html#34088" class="Datatype Operator">⦂</a> <a id="38799" href="plfa.part2.Lambda.html#30078" class="InductiveConstructor">`ℕ</a> <a id="38802" href="plfa.part2.Lambda.html#30051" class="InductiveConstructor Operator">⇒</a> <a id="38804" href="plfa.part2.Lambda.html#30078" class="InductiveConstructor">`ℕ</a>
<a id="38807" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#38772" class="Function">⊢sucᶜ</a> <a id="38813" class="Symbol">=</a> <a id="38815" href="plfa.part2.Lambda.html#34225" class="InductiveConstructor">⊢ƛ</a> <a id="38818" class="Symbol">(</a><a id="38819" href="plfa.part2.Lambda.html#34510" class="InductiveConstructor">⊢suc</a> <a id="38824" class="Symbol">(</a><a id="38825" href="plfa.part2.Lambda.html#34145" class="InductiveConstructor">⊢`</a> <a id="38828" href="plfa.part2.Lambda.html#38843" class="Function">∋n</a><a id="38830" class="Symbol">))</a>
  <a id="38835" class="Keyword">where</a>
  <a id="38843" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#38843" class="Function">∋n</a> <a id="38846" class="Symbol">=</a> <a id="38848" href="plfa.part2.Lambda.html#32967" class="InductiveConstructor">Z</a>

<a id="⊢2+2ᶜ"></a><a id="38851" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#38851" class="Function">⊢2+2ᶜ</a> <a id="38857" class="Symbol">:</a> <a id="38859" href="plfa.part2.Lambda.html#31712" class="InductiveConstructor">∅</a> <a id="38861" href="plfa.part2.Lambda.html#34088" class="Datatype Operator">⊢</a> <a id="38863" href="plfa.part2.Lambda.html#5834" class="Function">plusᶜ</a> <a id="38869" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="38871" href="plfa.part2.Lambda.html#5773" class="Function">twoᶜ</a> <a id="38876" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="38878" href="plfa.part2.Lambda.html#5773" class="Function">twoᶜ</a> <a id="38883" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="38885" href="plfa.part2.Lambda.html#5938" class="Function">sucᶜ</a> <a id="38890" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="38892" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a> <a id="38898" href="plfa.part2.Lambda.html#34088" class="Datatype Operator">⦂</a> <a id="38900" href="plfa.part2.Lambda.html#30078" class="InductiveConstructor">`ℕ</a>
<a id="38903" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#38851" class="Function">⊢2+2ᶜ</a> <a id="38909" class="Symbol">=</a> <a id="38911" href="plfa.part2.Lambda.html#38553" class="Function">⊢plusᶜ</a> <a id="38918" href="plfa.part2.Lambda.html#34332" class="InductiveConstructor Operator">·</a> <a id="38920" href="plfa.part2.Lambda.html#37380" class="Function">⊢twoᶜ</a> <a id="38926" href="plfa.part2.Lambda.html#34332" class="InductiveConstructor Operator">·</a> <a id="38928" href="plfa.part2.Lambda.html#37380" class="Function">⊢twoᶜ</a> <a id="38934" href="plfa.part2.Lambda.html#34332" class="InductiveConstructor Operator">·</a> <a id="38936" href="plfa.part2.Lambda.html#38772" class="Function">⊢sucᶜ</a> <a id="38942" href="plfa.part2.Lambda.html#34332" class="InductiveConstructor Operator">·</a> <a id="38944" href="plfa.part2.Lambda.html#34441" class="InductiveConstructor">⊢zero</a>
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
{% raw %}<pre class="Agda"><a id="∋-injective"></a><a id="40260" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#40260" class="Function">∋-injective</a> <a id="40272" class="Symbol">:</a> <a id="40274" class="Symbol">∀</a> <a id="40276" class="Symbol">{</a><a id="40277" href="plfa.part2.Lambda.html#40277" class="Bound">Γ</a> <a id="40279" href="plfa.part2.Lambda.html#40279" class="Bound">x</a> <a id="40281" href="plfa.part2.Lambda.html#40281" class="Bound">A</a> <a id="40283" href="plfa.part2.Lambda.html#40283" class="Bound">B</a><a id="40284" class="Symbol">}</a> <a id="40286" class="Symbol">→</a> <a id="40288" href="plfa.part2.Lambda.html#40277" class="Bound">Γ</a> <a id="40290" href="plfa.part2.Lambda.html#32924" class="Datatype Operator">∋</a> <a id="40292" href="plfa.part2.Lambda.html#40279" class="Bound">x</a> <a id="40294" href="plfa.part2.Lambda.html#32924" class="Datatype Operator">⦂</a> <a id="40296" href="plfa.part2.Lambda.html#40281" class="Bound">A</a> <a id="40298" class="Symbol">→</a> <a id="40300" href="plfa.part2.Lambda.html#40277" class="Bound">Γ</a> <a id="40302" href="plfa.part2.Lambda.html#32924" class="Datatype Operator">∋</a> <a id="40304" href="plfa.part2.Lambda.html#40279" class="Bound">x</a> <a id="40306" href="plfa.part2.Lambda.html#32924" class="Datatype Operator">⦂</a> <a id="40308" href="plfa.part2.Lambda.html#40283" class="Bound">B</a> <a id="40310" class="Symbol">→</a> <a id="40312" href="plfa.part2.Lambda.html#40281" class="Bound">A</a> <a id="40314" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="40316" href="plfa.part2.Lambda.html#40283" class="Bound">B</a>
<a id="40318" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#40260" class="Function">∋-injective</a> <a id="40330" href="plfa.part2.Lambda.html#32967" class="InductiveConstructor">Z</a>        <a id="40339" href="plfa.part2.Lambda.html#32967" class="InductiveConstructor">Z</a>          <a id="40350" class="Symbol">=</a>  <a id="40353" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>
<a id="40358" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#40260" class="Function">∋-injective</a> <a id="40370" href="plfa.part2.Lambda.html#32967" class="InductiveConstructor">Z</a>        <a id="40379" class="Symbol">(</a><a id="40380" href="plfa.part2.Lambda.html#33033" class="InductiveConstructor">S</a> <a id="40382" href="plfa.part2.Lambda.html#40382" class="Bound">x≢</a> <a id="40385" class="Symbol">_)</a>   <a id="40390" class="Symbol">=</a>  <a id="40393" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html#294" class="Function">⊥-elim</a> <a id="40400" class="Symbol">(</a><a id="40401" href="plfa.part2.Lambda.html#40382" class="Bound">x≢</a> <a id="40404" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a><a id="40408" class="Symbol">)</a>
<a id="40410" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#40260" class="Function">∋-injective</a> <a id="40422" class="Symbol">(</a><a id="40423" href="plfa.part2.Lambda.html#33033" class="InductiveConstructor">S</a> <a id="40425" href="plfa.part2.Lambda.html#40425" class="Bound">x≢</a> <a id="40428" class="Symbol">_)</a> <a id="40431" href="plfa.part2.Lambda.html#32967" class="InductiveConstructor">Z</a>          <a id="40442" class="Symbol">=</a>  <a id="40445" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html#294" class="Function">⊥-elim</a> <a id="40452" class="Symbol">(</a><a id="40453" href="plfa.part2.Lambda.html#40425" class="Bound">x≢</a> <a id="40456" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a><a id="40460" class="Symbol">)</a>
<a id="40462" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#40260" class="Function">∋-injective</a> <a id="40474" class="Symbol">(</a><a id="40475" href="plfa.part2.Lambda.html#33033" class="InductiveConstructor">S</a> <a id="40477" class="Symbol">_</a> <a id="40479" href="plfa.part2.Lambda.html#40479" class="Bound">∋x</a><a id="40481" class="Symbol">)</a> <a id="40483" class="Symbol">(</a><a id="40484" href="plfa.part2.Lambda.html#33033" class="InductiveConstructor">S</a> <a id="40486" class="Symbol">_</a> <a id="40488" href="plfa.part2.Lambda.html#40488" class="Bound">∋x′</a><a id="40491" class="Symbol">)</a>  <a id="40494" class="Symbol">=</a>  <a id="40497" href="plfa.part2.Lambda.html#40260" class="Function">∋-injective</a> <a id="40509" href="plfa.part2.Lambda.html#40479" class="Bound">∋x</a> <a id="40512" href="plfa.part2.Lambda.html#40488" class="Bound">∋x′</a>
</pre>{% endraw %}
The typing relation `Γ ⊢ M ⦂ A` is not injective. For example, in any `Γ`
the term `ƛ "x" ⇒ "x"` has type `A ⇒ A` for any type `A`.

### Non-examples

We can also show that terms are _not_ typeable.  For example, here is
a formal proof that it is not possible to type the term
`` `zero · `suc `zero ``.  It cannot be typed, because doing so
requires that the first term in the application is both a natural and
a function:

{% raw %}<pre class="Agda"><a id="nope₁"></a><a id="40949" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#40949" class="Function">nope₁</a> <a id="40955" class="Symbol">:</a> <a id="40957" class="Symbol">∀</a> <a id="40959" class="Symbol">{</a><a id="40960" href="plfa.part2.Lambda.html#40960" class="Bound">A</a><a id="40961" class="Symbol">}</a> <a id="40963" class="Symbol">→</a> <a id="40965" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#535" class="Function Operator">¬</a> <a id="40967" class="Symbol">(</a><a id="40968" href="plfa.part2.Lambda.html#31712" class="InductiveConstructor">∅</a> <a id="40970" href="plfa.part2.Lambda.html#34088" class="Datatype Operator">⊢</a> <a id="40972" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a> <a id="40978" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="40980" href="plfa.part2.Lambda.html#3982" class="InductiveConstructor Operator">`suc</a> <a id="40985" href="plfa.part2.Lambda.html#3948" class="InductiveConstructor">`zero</a> <a id="40991" href="plfa.part2.Lambda.html#34088" class="Datatype Operator">⦂</a> <a id="40993" href="plfa.part2.Lambda.html#40960" class="Bound">A</a><a id="40994" class="Symbol">)</a>
<a id="40996" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#40949" class="Function">nope₁</a> <a id="41002" class="Symbol">(()</a> <a id="41006" href="plfa.part2.Lambda.html#34332" class="InductiveConstructor Operator">·</a> <a id="41008" class="Symbol">_)</a>
</pre>{% endraw %}
As a second example, here is a formal proof that it is not possible to
type `` ƛ "x" ⇒ ` "x" · ` "x" ``. It cannot be typed, because
doing so requires types `A` and `B` such that `A ⇒ B ≡ A`:

{% raw %}<pre class="Agda"><a id="nope₂"></a><a id="41213" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#41213" class="Function">nope₂</a> <a id="41219" class="Symbol">:</a> <a id="41221" class="Symbol">∀</a> <a id="41223" class="Symbol">{</a><a id="41224" href="plfa.part2.Lambda.html#41224" class="Bound">A</a><a id="41225" class="Symbol">}</a> <a id="41227" class="Symbol">→</a> <a id="41229" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#535" class="Function Operator">¬</a> <a id="41231" class="Symbol">(</a><a id="41232" href="plfa.part2.Lambda.html#31712" class="InductiveConstructor">∅</a> <a id="41234" href="plfa.part2.Lambda.html#34088" class="Datatype Operator">⊢</a> <a id="41236" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">ƛ</a> <a id="41238" class="String">&quot;x&quot;</a> <a id="41242" href="plfa.part2.Lambda.html#3854" class="InductiveConstructor Operator">⇒</a> <a id="41244" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="41246" class="String">&quot;x&quot;</a> <a id="41250" href="plfa.part2.Lambda.html#3900" class="InductiveConstructor Operator">·</a> <a id="41252" href="plfa.part2.Lambda.html#3815" class="InductiveConstructor Operator">`</a> <a id="41254" class="String">&quot;x&quot;</a> <a id="41258" href="plfa.part2.Lambda.html#34088" class="Datatype Operator">⦂</a> <a id="41260" href="plfa.part2.Lambda.html#41224" class="Bound">A</a><a id="41261" class="Symbol">)</a>
<a id="41263" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#41213" class="Function">nope₂</a> <a id="41269" class="Symbol">(</a><a id="41270" href="plfa.part2.Lambda.html#34225" class="InductiveConstructor">⊢ƛ</a> <a id="41273" class="Symbol">(</a><a id="41274" href="plfa.part2.Lambda.html#34145" class="InductiveConstructor">⊢`</a> <a id="41277" href="plfa.part2.Lambda.html#41277" class="Bound">∋x</a> <a id="41280" href="plfa.part2.Lambda.html#34332" class="InductiveConstructor Operator">·</a> <a id="41282" href="plfa.part2.Lambda.html#34145" class="InductiveConstructor">⊢`</a> <a id="41285" href="plfa.part2.Lambda.html#41285" class="Bound">∋x′</a><a id="41288" class="Symbol">))</a>  <a id="41292" class="Symbol">=</a>  <a id="41295" href="plfa.part2.Lambda.html#41340" class="Function">contradiction</a> <a id="41309" class="Symbol">(</a><a id="41310" href="plfa.part2.Lambda.html#40260" class="Function">∋-injective</a> <a id="41322" href="plfa.part2.Lambda.html#41277" class="Bound">∋x</a> <a id="41325" href="plfa.part2.Lambda.html#41285" class="Bound">∋x′</a><a id="41328" class="Symbol">)</a>
  <a id="41332" class="Keyword">where</a>
  <a id="41340" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#41340" class="Function">contradiction</a> <a id="41354" class="Symbol">:</a> <a id="41356" class="Symbol">∀</a> <a id="41358" class="Symbol">{</a><a id="41359" href="plfa.part2.Lambda.html#41359" class="Bound">A</a> <a id="41361" href="plfa.part2.Lambda.html#41361" class="Bound">B</a><a id="41362" class="Symbol">}</a> <a id="41364" class="Symbol">→</a> <a id="41366" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#535" class="Function Operator">¬</a> <a id="41368" class="Symbol">(</a><a id="41369" href="plfa.part2.Lambda.html#41359" class="Bound">A</a> <a id="41371" href="plfa.part2.Lambda.html#30051" class="InductiveConstructor Operator">⇒</a> <a id="41373" href="plfa.part2.Lambda.html#41361" class="Bound">B</a> <a id="41375" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="41377" href="plfa.part2.Lambda.html#41359" class="Bound">A</a><a id="41378" class="Symbol">)</a>
  <a id="41382" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part2/Lambda.md %}{% raw %}#41340" class="Function">contradiction</a> <a id="41396" class="Symbol">()</a>
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


#### Exercise `⊢mul` (recommended)

Using the term `mul` you defined earlier, write out the derivation
showing that it is well typed.

{% raw %}<pre class="Agda"><a id="42071" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}

#### Exercise `⊢mulᶜ` (practice)

Using the term `mulᶜ` you defined earlier, write out the derivation
showing that it is well typed.

{% raw %}<pre class="Agda"><a id="42238" class="Comment">-- Your code goes here</a>
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
