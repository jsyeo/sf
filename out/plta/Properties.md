---
title     : "Properties: Proof by Induction"
layout    : page
permalink : /Properties/
---

<pre class="Agda">{% raw %}<a id="110" class="Keyword">module</a> <a id="117" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Properties.md %}{% raw %}" class="Module">plta.Properties</a> <a id="133" class="Keyword">where</a>{% endraw %}</pre>

Now that we've defined the naturals and operations upon them, our next
step is to learn how to prove properties that they satisfy.  As hinted
by their name, properties of *inductive datatypes* are proved by
*induction*.


## Imports

We require equivality as in the previous chapter, plus the naturals
and some operations upon them.  We also import a couple of new operations,
`cong`, `sym`, and `_≡⟨_⟩_`, which are explained below.
<pre class="Agda">{% raw %}<a id="597" class="Keyword">import</a> <a id="604" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html" class="Module">Relation.Binary.PropositionalEquality</a> <a id="642" class="Symbol">as</a> <a id="645" class="Module">Eq</a>
<a id="648" class="Keyword">open</a> <a id="653" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html" class="Module">Eq</a> <a id="656" class="Keyword">using</a> <a id="662" class="Symbol">(</a><a id="663" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator">_≡_</a><a id="666" class="Symbol">;</a> <a id="668" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor">refl</a><a id="672" class="Symbol">;</a> <a id="674" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#1075" class="Function">cong</a><a id="678" class="Symbol">;</a> <a id="680" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.Core.html#560" class="Function">sym</a><a id="683" class="Symbol">)</a>
<a id="685" class="Keyword">open</a> <a id="690" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#3861" class="Module">Eq.≡-Reasoning</a> <a id="705" class="Keyword">using</a> <a id="711" class="Symbol">(</a><a id="712" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#3962" class="Function Operator">begin_</a><a id="718" class="Symbol">;</a> <a id="720" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4020" class="Function Operator">_≡⟨⟩_</a><a id="725" class="Symbol">;</a> <a id="727" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4079" class="Function Operator">_≡⟨_⟩_</a><a id="733" class="Symbol">;</a> <a id="735" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4260" class="Function Operator">_∎</a><a id="737" class="Symbol">)</a>
<a id="739" class="Keyword">open</a> <a id="744" class="Keyword">import</a> <a id="751" href="https://agda.github.io/agda-stdlib/Data.Nat.html" class="Module">Data.Nat</a> <a id="760" class="Keyword">using</a> <a id="766" class="Symbol">(</a><a id="767" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="768" class="Symbol">;</a> <a id="770" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a><a id="774" class="Symbol">;</a> <a id="776" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a><a id="779" class="Symbol">;</a> <a id="781" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">_+_</a><a id="784" class="Symbol">;</a> <a id="786" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#433" class="Primitive Operator">_*_</a><a id="789" class="Symbol">;</a> <a id="791" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#320" class="Primitive Operator">_∸_</a><a id="794" class="Symbol">)</a>{% endraw %}</pre>


## Associativity

One property of addition is that it is *associative*, that is, that the
location of the parentheses does not matter:

    (m + n) + p ≡ m + (n + p)

Here `m`, `n`, and `p` are variables that range over all natural numbers.

We can test the proposition by choosing specific numbers for the three
variables.
<pre class="Agda">{% raw %}<a id="1146" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Properties.md %}{% raw %}#1146" class="Function">_</a> <a id="1148" class="Symbol">:</a> <a id="1150" class="Symbol">(</a><a id="1151" class="Number">3</a> <a id="1153" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="1155" class="Number">4</a><a id="1156" class="Symbol">)</a> <a id="1158" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="1160" class="Number">5</a> <a id="1162" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator">≡</a> <a id="1164" class="Number">3</a> <a id="1166" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="1168" class="Symbol">(</a><a id="1169" class="Number">4</a> <a id="1171" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="1173" class="Number">5</a><a id="1174" class="Symbol">)</a>
<a id="1176" class="Symbol">_</a> <a id="1178" class="Symbol">=</a>
  <a id="1182" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#3962" class="Function Operator">begin</a>
    <a id="1192" class="Symbol">(</a><a id="1193" class="Number">3</a> <a id="1195" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="1197" class="Number">4</a><a id="1198" class="Symbol">)</a> <a id="1200" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="1202" class="Number">5</a>
  <a id="1206" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4020" class="Function Operator">≡⟨⟩</a>
    <a id="1214" class="Number">7</a> <a id="1216" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="1218" class="Number">5</a>
  <a id="1222" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4020" class="Function Operator">≡⟨⟩</a>
    <a id="1230" class="Number">12</a>
  <a id="1235" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4020" class="Function Operator">≡⟨⟩</a>
    <a id="1243" class="Number">3</a> <a id="1245" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="1247" class="Number">9</a>
  <a id="1251" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4020" class="Function Operator">≡⟨⟩</a>
    <a id="1259" class="Number">3</a> <a id="1261" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="1263" class="Symbol">(</a><a id="1264" class="Number">4</a> <a id="1266" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="1268" class="Number">5</a><a id="1269" class="Symbol">)</a>
  <a id="1273" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4260" class="Function Operator">∎</a>{% endraw %}</pre>
Here we have displayed the computation as a chain of equations,
one term to a line.  It is often easiest to read such chains from the top down
until one reaches the simplest term (in this case, `12`), and
then from the bottom up until one reaches the same term.

The test reveals that associativity is perhaps not as obvious as first
it appears.  Why should `7 + 5` be the same as `3 + 9`?  We might want
to gather more evidence, testing the proposition by choosing other
numbers.  But---since there are an infinite number of
naturals---testing can never be complete.  Is there any way we can be
sure that associativity holds for *all* the natural numbers?

The answer is yes! We can prove a property holds for all naturals using
*proof by induction*.


## Proof by induction

Recall the definition of natural numbers consists of a *base case*
which tells us that `zero` is a natural, and an *inductive case*
which tells us that if `m` is a natural then `suc m` is also a natural.

Proof by induction follows the structure of this definition.  To prove
a property of natural numbers by induction, we need prove two cases.
First is the *base case*, where we show the property holds for `zero`.
Second is the *inductive case*, where we assume the the property holds for
an arbitrary natural `m` (we call this the *inductive hypothesis*), and
then show that the property must also hold for `suc m`.

If we write `P m` for a property of `m`, then what we need to
demonstrate are the following two inference rules:

    ------
    P zero

    P m
    ---------
    P (suc m)

Let's unpack these rules.  The first rule is the base case, and
requires we show that property `P` holds for `zero`.  The second rule
is the inductive case, and requires we show that if we assume the
inductive hypothesis, namely that `P` holds for `m`, then it follows that
`P` also holds for `suc m`.

Why does this work?  Again, it can be explained by a creation story.
To start with, we know no properties.

    -- in the beginning, no properties are known

Now, we apply the two rules to all the properties we know about.  The
base case tells us that `P zero` holds, so we add it to the set of
known properties.  The inductive case tells us that if `P m` holds (on
the day before today) then `P (suc m)` also holds (today).  We didn't
know about any properties before today, so the inductive case doesn't
apply.

    -- on the first day, one property is known
    P zero

Then we repeat the process, so on the next day we know about all the
properties from the day before, plus any properties added by the rules.
The base case tells us that `P zero` holds, but we already
knew that. But now the inductive case tells us that since `P zero`
held yesterday, then `P (suc zero)` holds today.

    -- on the second day, two properties are known
    P zero
    P (suc zero)

And we repeat the process again. Now the inductive case
tells us that since `P zero` and `P (suc zero)` both hold, then
`P (suc zero)` and `P (suc (suc zero))` also hold. We already knew about
the first of these, but the second is new.

    -- on the third day, three properties are known
    P zero
    P (suc zero)
    P (suc (suc zero))

You've got the hang of it by now.

    -- on the fourth day, four properties are known
    P zero
    P (suc zero)
    P (suc (suc zero))
    P (suc (suc (suc zero)))

The process continues.  On the *n*th day there will be *n* distinct
properties that hold.  The property of every natural number will appear
on some given day.  In particular, the property `P n` first appears on
day *n+1*.


## Our first proof: associativity

To prove associativity, we take `P m` to be the property

    (m + n) + p ≡ m + (n + p)

Here `n` and `p` are arbitrary natural numbers, so if we can show the
equation holds for all `m` it will also hold for all `n` and `p`.
The appropriate instances of the inference rules are:

    -------------------------------
    (zero + n) + p ≡ zero + (n + p)

    (m + n) + p ≡ m + (n + p)
    ---------------------------------
    (suc m + n) + p ≡ suc m + (n + p)

If we can demonstrate both of these, then associativity of addition
follows by induction.

Here is the proposition's statement and proof.
<pre class="Agda">{% raw %}<a id="+-assoc"></a><a id="5509" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Properties.md %}{% raw %}#5509" class="Function">+-assoc</a> <a id="5517" class="Symbol">:</a> <a id="5519" class="Symbol">∀</a> <a id="5521" class="Symbol">(</a><a id="5522" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Properties.md %}{% raw %}#5522" class="Bound">m</a> <a id="5524" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Properties.md %}{% raw %}#5524" class="Bound">n</a> <a id="5526" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Properties.md %}{% raw %}#5526" class="Bound">p</a> <a id="5528" class="Symbol">:</a> <a id="5530" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="5531" class="Symbol">)</a> <a id="5533" class="Symbol">→</a> <a id="5535" class="Symbol">(</a><a id="5536" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Properties.md %}{% raw %}#5522" class="Bound">m</a> <a id="5538" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="5540" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Properties.md %}{% raw %}#5524" class="Bound">n</a><a id="5541" class="Symbol">)</a> <a id="5543" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="5545" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Properties.md %}{% raw %}#5526" class="Bound">p</a> <a id="5547" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator">≡</a> <a id="5549" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Properties.md %}{% raw %}#5522" class="Bound">m</a> <a id="5551" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="5553" class="Symbol">(</a><a id="5554" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Properties.md %}{% raw %}#5524" class="Bound">n</a> <a id="5556" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="5558" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Properties.md %}{% raw %}#5526" class="Bound">p</a><a id="5559" class="Symbol">)</a>
<a id="5561" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Properties.md %}{% raw %}#5509" class="Function">+-assoc</a> <a id="5569" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a> <a id="5574" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Properties.md %}{% raw %}#5574" class="Bound">n</a> <a id="5576" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Properties.md %}{% raw %}#5576" class="Bound">p</a> <a id="5578" class="Symbol">=</a>
  <a id="5582" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#3962" class="Function Operator">begin</a>
    <a id="5592" class="Symbol">(</a><a id="5593" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a> <a id="5598" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="5600" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Properties.md %}{% raw %}#5574" class="Bound">n</a><a id="5601" class="Symbol">)</a> <a id="5603" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="5605" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Properties.md %}{% raw %}#5576" class="Bound">p</a>
  <a id="5609" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4020" class="Function Operator">≡⟨⟩</a>
    <a id="5617" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Properties.md %}{% raw %}#5574" class="Bound">n</a> <a id="5619" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="5621" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Properties.md %}{% raw %}#5576" class="Bound">p</a>
  <a id="5625" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4020" class="Function Operator">≡⟨⟩</a>
   <a id="5632" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a> <a id="5637" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="5639" class="Symbol">(</a><a id="5640" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Properties.md %}{% raw %}#5574" class="Bound">n</a> <a id="5642" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="5644" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Properties.md %}{% raw %}#5576" class="Bound">p</a><a id="5645" class="Symbol">)</a>
  <a id="5649" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4260" class="Function Operator">∎</a>
<a id="5651" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Properties.md %}{% raw %}#5509" class="Function">+-assoc</a> <a id="5659" class="Symbol">(</a><a id="5660" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="5664" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Properties.md %}{% raw %}#5664" class="Bound">m</a><a id="5665" class="Symbol">)</a> <a id="5667" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Properties.md %}{% raw %}#5667" class="Bound">n</a> <a id="5669" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Properties.md %}{% raw %}#5669" class="Bound">p</a> <a id="5671" class="Symbol">=</a>
  <a id="5675" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#3962" class="Function Operator">begin</a>
    <a id="5685" class="Symbol">(</a><a id="5686" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="5690" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Properties.md %}{% raw %}#5664" class="Bound">m</a> <a id="5692" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="5694" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Properties.md %}{% raw %}#5667" class="Bound">n</a><a id="5695" class="Symbol">)</a> <a id="5697" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="5699" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Properties.md %}{% raw %}#5669" class="Bound">p</a>
  <a id="5703" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4020" class="Function Operator">≡⟨⟩</a>
    <a id="5711" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="5715" class="Symbol">(</a><a id="5716" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Properties.md %}{% raw %}#5664" class="Bound">m</a> <a id="5718" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="5720" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Properties.md %}{% raw %}#5667" class="Bound">n</a><a id="5721" class="Symbol">)</a> <a id="5723" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="5725" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Properties.md %}{% raw %}#5669" class="Bound">p</a>
  <a id="5729" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4020" class="Function Operator">≡⟨⟩</a>
    <a id="5737" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="5741" class="Symbol">((</a><a id="5743" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Properties.md %}{% raw %}#5664" class="Bound">m</a> <a id="5745" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="5747" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Properties.md %}{% raw %}#5667" class="Bound">n</a><a id="5748" class="Symbol">)</a> <a id="5750" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="5752" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Properties.md %}{% raw %}#5669" class="Bound">p</a><a id="5753" class="Symbol">)</a>
  <a id="5757" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4079" class="Function Operator">≡⟨</a> <a id="5760" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#1075" class="Function">cong</a> <a id="5765" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="5769" class="Symbol">(</a><a id="5770" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Properties.md %}{% raw %}#5509" class="Function">+-assoc</a> <a id="5778" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Properties.md %}{% raw %}#5664" class="Bound">m</a> <a id="5780" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Properties.md %}{% raw %}#5667" class="Bound">n</a> <a id="5782" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Properties.md %}{% raw %}#5669" class="Bound">p</a><a id="5783" class="Symbol">)</a> <a id="5785" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4079" class="Function Operator">⟩</a>
    <a id="5791" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="5795" class="Symbol">(</a><a id="5796" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Properties.md %}{% raw %}#5664" class="Bound">m</a> <a id="5798" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="5800" class="Symbol">(</a><a id="5801" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Properties.md %}{% raw %}#5667" class="Bound">n</a> <a id="5803" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="5805" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Properties.md %}{% raw %}#5669" class="Bound">p</a><a id="5806" class="Symbol">))</a>
  <a id="5811" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4020" class="Function Operator">≡⟨⟩</a>
    <a id="5819" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="5823" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Properties.md %}{% raw %}#5664" class="Bound">m</a> <a id="5825" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="5827" class="Symbol">(</a><a id="5828" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Properties.md %}{% raw %}#5667" class="Bound">n</a> <a id="5830" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="5832" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Properties.md %}{% raw %}#5669" class="Bound">p</a><a id="5833" class="Symbol">)</a>
  <a id="5837" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4260" class="Function Operator">∎</a>{% endraw %}</pre>
We have named the proof `+-assoc`.  In Agda, identifiers can consist of
any sequence of characters not including spaces or the characters `@.(){};_`.

Let's unpack this code.  The signature states that we are
defining the identifier `+-assoc` which provide evidence for the
proposition:

    ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)

The upside down A is pronounced "for all", and the proposition
asserts that for all natural numbers `m`, `n`, and `p` that
the equation `(m + n) + p ≡ m + (n + p)` holds.  Evidence for the proposition
is a function that accepts three natural numbers, binds them to `m`, `n`, and `p`,
and returns evidence for the corresponding instance of the equation.

For the base case, we must show:

    (zero + n) + p ≡ zero + (n + p)

Simplifying both sides with the base case of addition yields the equation:

    n + p ≡ n + p

This holds trivially.  Reading the chain of equations in the base case of the proof,
the top and bottom of the chain match the two sides of the equation to
be shown, and reading down from the top and up from the bottom takes us to
`n + p` in the middle.  No justification other than simplification is required.

For the inductive case, we must show:

    (suc m + n) + p ≡ suc m + (n + p)

Simplifying both sides with the inductive case of addition yields the equation:

    suc ((m + n) + p) ≡ suc (m + (n + p))

This in turn follows by prefacing `suc` to both sides of the induction
hypothesis:

    (m + n) + p ≡ m + (n + p)

Reading the chain of equations in the inductive case of the proof, the
top and bottom of the chain match the two sides of the equation to be
shown, and reading down from the top and up from the bottom takes us
to the simplified equation above. The remaining equation, does not follow
from simplification alone, so we use an additional operator for chain
reasoning, `_≡⟨_⟩_`, where a justification for the equation appears
within angle brackets.  The justification given is:

    ⟨ cong suc (+-assoc m n p) ⟩

Here, the recursive invocation `+-assoc m n p` has as its type the
induction hypothesis, and `cong suc` prefaces `suc` to each side to
yield the needed equation.

A relation is said to be a *congruence* for a given function if it is
preserved by applying that function.  If `e` is evidence that `x ≡ y`,
then `cong f e` is evidence that `f x ≡ f y`, for any function `f`.

Here the inductive hypothesis is not assumed, but instead proved by a
recursive invocation of the function we are defining, `+-assoc m n p`.
As with addition, this is well founded because associativity of
larger numbers is proved in terms of associativity of smaller numbers.
In this case, `assoc (suc m) n p` is proved using `assoc m n p`.
The correspondence between proof by induction and definition by
recursion is one of the most appealing aspects of Agda.


## Our second proof: commutativity

Another important property of addition is that it is *commutative*, that is,
that the order of the operands does not matter:

    m + n ≡ n + m

The proof requires that we first demonstrate two lemmas.

### The first lemma

The base case of the definition of addition states that zero
is a left-identity:

    zero + n ≡ n

Our first lemma states that zero is also a right-identity:

    m + zero ≡ m

Here is the lemma's statement and proof.
<pre class="Agda">{% raw %}<a id="+-identityʳ"></a><a id="9171" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Properties.md %}{% raw %}#9171" class="Function">+-identityʳ</a> <a id="9183" class="Symbol">:</a> <a id="9185" class="Symbol">∀</a> <a id="9187" class="Symbol">(</a><a id="9188" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Properties.md %}{% raw %}#9188" class="Bound">m</a> <a id="9190" class="Symbol">:</a> <a id="9192" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="9193" class="Symbol">)</a> <a id="9195" class="Symbol">→</a> <a id="9197" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Properties.md %}{% raw %}#9188" class="Bound">m</a> <a id="9199" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="9201" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a> <a id="9206" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator">≡</a> <a id="9208" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Properties.md %}{% raw %}#9188" class="Bound">m</a>
<a id="9210" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Properties.md %}{% raw %}#9171" class="Function">+-identityʳ</a> <a id="9222" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a> <a id="9227" class="Symbol">=</a>
  <a id="9231" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#3962" class="Function Operator">begin</a>
    <a id="9241" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a> <a id="9246" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="9248" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a>
  <a id="9255" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4020" class="Function Operator">≡⟨⟩</a>
    <a id="9263" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a>
  <a id="9270" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4260" class="Function Operator">∎</a>
<a id="9272" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Properties.md %}{% raw %}#9171" class="Function">+-identityʳ</a> <a id="9284" class="Symbol">(</a><a id="9285" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="9289" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Properties.md %}{% raw %}#9289" class="Bound">m</a><a id="9290" class="Symbol">)</a> <a id="9292" class="Symbol">=</a>
  <a id="9296" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#3962" class="Function Operator">begin</a>
    <a id="9306" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="9310" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Properties.md %}{% raw %}#9289" class="Bound">m</a> <a id="9312" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="9314" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a>
  <a id="9321" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4020" class="Function Operator">≡⟨⟩</a>
    <a id="9329" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="9333" class="Symbol">(</a><a id="9334" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Properties.md %}{% raw %}#9289" class="Bound">m</a> <a id="9336" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="9338" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a><a id="9342" class="Symbol">)</a>
  <a id="9346" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4079" class="Function Operator">≡⟨</a> <a id="9349" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#1075" class="Function">cong</a> <a id="9354" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="9358" class="Symbol">(</a><a id="9359" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Properties.md %}{% raw %}#9171" class="Function">+-identityʳ</a> <a id="9371" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Properties.md %}{% raw %}#9289" class="Bound">m</a><a id="9372" class="Symbol">)</a> <a id="9374" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4079" class="Function Operator">⟩</a>
    <a id="9380" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="9384" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Properties.md %}{% raw %}#9289" class="Bound">m</a>
  <a id="9388" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4260" class="Function Operator">∎</a>{% endraw %}</pre>
The signature states that we are defining the identifier `+-identityʳ` which
provides evidence for the proposition:

    ∀ (m : ℕ) → m + zero ≡ m

Evidence for the proposition is a function that accepts a natural
number, binds it to `m`, and returns evidence for the corresponding
instance of the equation.  The proof is by induction on `m`.

For the base case, we must show:

    zero + zero ≡ zero

Simplifying with the base case of of addition, this is straightforward.

For the inductive case, we must show:

    (suc m) + zero = suc m

Simplifying both sides with the inductive case of addition yields the equation:

    suc (m + zero) = suc m

This in turn follows by prefacing `suc` to both sides of the induction
hypothesis:

    m + zero ≡ m

Reading the chain of equations down from the top and up from the bottom
takes us to the simplified equation above.  The remaining
equation has the justification:

    ⟨ cong suc (+-identityʳ m) ⟩

Here, the recursive invocation `+-identityʳ m` has as its type the
induction hypothesis, and `cong suc` prefaces `suc` to each side to
yield the needed equation.  This completes the first lemma.

### The second lemma

The inductive case of the definition of addition pushes `suc` on the
first argument to the outside:

    suc m + n ≡ suc (m + n)

Our second lemma does the same for `suc` on the second argument:

    m + suc n ≡ suc (m + n)

Here is the lemma's statement and proof.
<pre class="Agda">{% raw %}<a id="+-suc"></a><a id="10847" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Properties.md %}{% raw %}#10847" class="Function">+-suc</a> <a id="10853" class="Symbol">:</a> <a id="10855" class="Symbol">∀</a> <a id="10857" class="Symbol">(</a><a id="10858" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Properties.md %}{% raw %}#10858" class="Bound">m</a> <a id="10860" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Properties.md %}{% raw %}#10860" class="Bound">n</a> <a id="10862" class="Symbol">:</a> <a id="10864" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="10865" class="Symbol">)</a> <a id="10867" class="Symbol">→</a> <a id="10869" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Properties.md %}{% raw %}#10858" class="Bound">m</a> <a id="10871" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="10873" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="10877" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Properties.md %}{% raw %}#10860" class="Bound">n</a> <a id="10879" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator">≡</a> <a id="10881" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="10885" class="Symbol">(</a><a id="10886" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Properties.md %}{% raw %}#10858" class="Bound">m</a> <a id="10888" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="10890" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Properties.md %}{% raw %}#10860" class="Bound">n</a><a id="10891" class="Symbol">)</a>
<a id="10893" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Properties.md %}{% raw %}#10847" class="Function">+-suc</a> <a id="10899" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a> <a id="10904" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Properties.md %}{% raw %}#10904" class="Bound">n</a> <a id="10906" class="Symbol">=</a>
  <a id="10910" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#3962" class="Function Operator">begin</a>
    <a id="10920" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a> <a id="10925" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="10927" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="10931" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Properties.md %}{% raw %}#10904" class="Bound">n</a>
  <a id="10935" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4020" class="Function Operator">≡⟨⟩</a>
    <a id="10943" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="10947" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Properties.md %}{% raw %}#10904" class="Bound">n</a>
  <a id="10951" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4020" class="Function Operator">≡⟨⟩</a>
    <a id="10959" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="10963" class="Symbol">(</a><a id="10964" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a> <a id="10969" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="10971" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Properties.md %}{% raw %}#10904" class="Bound">n</a><a id="10972" class="Symbol">)</a>
  <a id="10976" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4260" class="Function Operator">∎</a>
<a id="10978" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Properties.md %}{% raw %}#10847" class="Function">+-suc</a> <a id="10984" class="Symbol">(</a><a id="10985" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="10989" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Properties.md %}{% raw %}#10989" class="Bound">m</a><a id="10990" class="Symbol">)</a> <a id="10992" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Properties.md %}{% raw %}#10992" class="Bound">n</a> <a id="10994" class="Symbol">=</a>
  <a id="10998" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#3962" class="Function Operator">begin</a>
    <a id="11008" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="11012" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Properties.md %}{% raw %}#10989" class="Bound">m</a> <a id="11014" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="11016" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="11020" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Properties.md %}{% raw %}#10992" class="Bound">n</a>
  <a id="11024" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4020" class="Function Operator">≡⟨⟩</a>
    <a id="11032" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="11036" class="Symbol">(</a><a id="11037" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Properties.md %}{% raw %}#10989" class="Bound">m</a> <a id="11039" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="11041" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="11045" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Properties.md %}{% raw %}#10992" class="Bound">n</a><a id="11046" class="Symbol">)</a>
  <a id="11050" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4079" class="Function Operator">≡⟨</a> <a id="11053" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#1075" class="Function">cong</a> <a id="11058" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="11062" class="Symbol">(</a><a id="11063" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Properties.md %}{% raw %}#10847" class="Function">+-suc</a> <a id="11069" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Properties.md %}{% raw %}#10989" class="Bound">m</a> <a id="11071" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Properties.md %}{% raw %}#10992" class="Bound">n</a><a id="11072" class="Symbol">)</a> <a id="11074" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4079" class="Function Operator">⟩</a>
    <a id="11080" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="11084" class="Symbol">(</a><a id="11085" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="11089" class="Symbol">(</a><a id="11090" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Properties.md %}{% raw %}#10989" class="Bound">m</a> <a id="11092" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="11094" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Properties.md %}{% raw %}#10992" class="Bound">n</a><a id="11095" class="Symbol">))</a>
  <a id="11100" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4020" class="Function Operator">≡⟨⟩</a>
    <a id="11108" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="11112" class="Symbol">(</a><a id="11113" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="11117" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Properties.md %}{% raw %}#10989" class="Bound">m</a> <a id="11119" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="11121" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Properties.md %}{% raw %}#10992" class="Bound">n</a><a id="11122" class="Symbol">)</a>
  <a id="11126" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4260" class="Function Operator">∎</a>{% endraw %}</pre>
The signature states that we are defining the identifier `+-suc` which provides
evidence for the proposition:

    ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)

Evidence for the proposition is a function that accepts two natural numbers,
binds them to `m` and `n`, and returns evidence for the corresponding instance
of the equation.  The proof is by induction on `m`.

For the base case, we must show:

    zero + suc n ≡ suc (zero + n)

Simplifying with the base case of of addition, this is straightforward.

For the inductive case, we must show:

    suc m + suc n ≡ suc (suc m + n)

Simplifying both sides with the inductive case of addition yields the equation:

    suc (m + suc n) ≡ suc (suc (m + n))

This in turn follows by prefacing `suc` to both sides of the induction
hypothesis:

    m + suc n ≡ suc (m + n)

Reading the chain of equations down from the top and up from the bottom
takes us to the simplified equation in the middle.  The remaining
equation has the justification:

    ⟨ cong suc (+-suc m n) ⟩

Here, the recursive invocation `+-suc m n` has as its type the
induction hypothesis, and `cong suc` prefaces `suc` to each side to
yield the needed equation.  This completes the second lemma.

### The proposition

Finally, here is our proposition's statement and proof.
<pre class="Agda">{% raw %}<a id="+-comm"></a><a id="12439" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Properties.md %}{% raw %}#12439" class="Function">+-comm</a> <a id="12446" class="Symbol">:</a> <a id="12448" class="Symbol">∀</a> <a id="12450" class="Symbol">(</a><a id="12451" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Properties.md %}{% raw %}#12451" class="Bound">m</a> <a id="12453" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Properties.md %}{% raw %}#12453" class="Bound">n</a> <a id="12455" class="Symbol">:</a> <a id="12457" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="12458" class="Symbol">)</a> <a id="12460" class="Symbol">→</a> <a id="12462" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Properties.md %}{% raw %}#12451" class="Bound">m</a> <a id="12464" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="12466" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Properties.md %}{% raw %}#12453" class="Bound">n</a> <a id="12468" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator">≡</a> <a id="12470" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Properties.md %}{% raw %}#12453" class="Bound">n</a> <a id="12472" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="12474" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Properties.md %}{% raw %}#12451" class="Bound">m</a>
<a id="12476" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Properties.md %}{% raw %}#12439" class="Function">+-comm</a> <a id="12483" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Properties.md %}{% raw %}#12483" class="Bound">m</a> <a id="12485" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a> <a id="12490" class="Symbol">=</a>
  <a id="12494" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#3962" class="Function Operator">begin</a>
    <a id="12504" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Properties.md %}{% raw %}#12483" class="Bound">m</a> <a id="12506" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="12508" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a>
  <a id="12515" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4079" class="Function Operator">≡⟨</a> <a id="12518" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Properties.md %}{% raw %}#9171" class="Function">+-identityʳ</a> <a id="12530" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Properties.md %}{% raw %}#12483" class="Bound">m</a> <a id="12532" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4079" class="Function Operator">⟩</a>
    <a id="12538" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Properties.md %}{% raw %}#12483" class="Bound">m</a>
  <a id="12542" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4020" class="Function Operator">≡⟨⟩</a>
    <a id="12550" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a> <a id="12555" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="12557" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Properties.md %}{% raw %}#12483" class="Bound">m</a>
  <a id="12561" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4260" class="Function Operator">∎</a>
<a id="12563" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Properties.md %}{% raw %}#12439" class="Function">+-comm</a> <a id="12570" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Properties.md %}{% raw %}#12570" class="Bound">m</a> <a id="12572" class="Symbol">(</a><a id="12573" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="12577" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Properties.md %}{% raw %}#12577" class="Bound">n</a><a id="12578" class="Symbol">)</a> <a id="12580" class="Symbol">=</a>
  <a id="12584" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#3962" class="Function Operator">begin</a>
    <a id="12594" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Properties.md %}{% raw %}#12570" class="Bound">m</a> <a id="12596" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="12598" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="12602" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Properties.md %}{% raw %}#12577" class="Bound">n</a>
  <a id="12606" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4079" class="Function Operator">≡⟨</a> <a id="12609" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Properties.md %}{% raw %}#10847" class="Function">+-suc</a> <a id="12615" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Properties.md %}{% raw %}#12570" class="Bound">m</a> <a id="12617" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Properties.md %}{% raw %}#12577" class="Bound">n</a> <a id="12619" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4079" class="Function Operator">⟩</a>
    <a id="12625" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="12629" class="Symbol">(</a><a id="12630" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Properties.md %}{% raw %}#12570" class="Bound">m</a> <a id="12632" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="12634" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Properties.md %}{% raw %}#12577" class="Bound">n</a><a id="12635" class="Symbol">)</a>
  <a id="12639" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4079" class="Function Operator">≡⟨</a> <a id="12642" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#1075" class="Function">cong</a> <a id="12647" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="12651" class="Symbol">(</a><a id="12652" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Properties.md %}{% raw %}#12439" class="Function">+-comm</a> <a id="12659" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Properties.md %}{% raw %}#12570" class="Bound">m</a> <a id="12661" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Properties.md %}{% raw %}#12577" class="Bound">n</a><a id="12662" class="Symbol">)</a> <a id="12664" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4079" class="Function Operator">⟩</a>
    <a id="12670" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="12674" class="Symbol">(</a><a id="12675" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Properties.md %}{% raw %}#12577" class="Bound">n</a> <a id="12677" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="12679" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Properties.md %}{% raw %}#12570" class="Bound">m</a><a id="12680" class="Symbol">)</a>
  <a id="12684" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4020" class="Function Operator">≡⟨⟩</a>
    <a id="12692" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="12696" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Properties.md %}{% raw %}#12577" class="Bound">n</a> <a id="12698" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="12700" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Properties.md %}{% raw %}#12570" class="Bound">m</a>
  <a id="12704" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4260" class="Function Operator">∎</a>{% endraw %}</pre>
The first line states that we are defining the identifier
`+-comm` which provides evidence for the proposition:

    ∀ (m n : ℕ) → m + n ≡ n + m

Evidence for the proposition is a function that accepts two
natural numbers, binds them to `m` and `n`, and returns evidence for the
corresponding instance of the equation.  The proof is by
induction on `n`.  (Not on `m` this time!)

For the base case, we must show:

    m + zero ≡ zero + m

Simplifying both sides with the base case of addition yields the equation:

    m + zero ≡ m

The the remaining equation has the justification

    ⟨ +-identityʳ m ⟩

which invokes the first lemma.

For the inductive case, we must show:

    m + suc n ≡ suc n + m

Simplifying both sides with the inductive case of addition yields the equation:

    m + suc n ≡ suc (n + m)

We show this in two steps.  First, we have:

    m + suc n ≡ suc (m + n)

which is justified by the second lemma, `⟨ +-suc m n ⟩`.  Then we
have

    suc (m + n) ≡ suc (n + m)

which is justified by congruence and the induction hypothesis,
`⟨ cong suc (+-comm m n) ⟩`.  This completes the proposition.

Agda requires that identifiers are defined before they are used,
so we must present the lemmas before the main proposition, as we
have done above.  In practice, one will often attempt to prove
the main proposition first, and the equations required to do so
will suggest what lemmas to prove.



## Creation, one last time

Returning to the proof of associativity, it may be helpful to view the inductive
proof (or, equivalently, the recursive definition) as a creation story.  This
time we are concerned with judgements asserting associativity.

     -- in the beginning, we know nothing about associativity

Now, we apply the rules to all the judgements we know about.  The base
case tells us that `(zero + n) + p ≡ zero + (n + p)` for every natural
`n` and `p`.  The inductive case tells us that if `(m + n) + p ≡ m +
(n + p)` (on the day before today) then `(suc m + n) + p ≡ suc m + (n
+ p)` (today).  We didn't know any judgments about associativity
before today, so that rule doesn't give us any new judgments.

    -- on the first day, we know about associativity of 0
    (0 + 0) + 0 ≡ 0 + (0 + 0)   ...   (0 + 4) + 5 ≡ 0 + (4 + 5)   ...

Then we repeat the process, so on the next day we know about all the
judgements from the day before, plus any judgements added by the rules.
The base case tells us nothing new, but now the inductive case adds
more judgements.

    -- on the second day, we know about associativity of 0 and 1
    (0 + 0) + 0 ≡ 0 + (0 + 0)   ...   (0 + 4) + 5 ≡ 0 + (4 + 5)   ...
    (1 + 0) + 0 ≡ 1 + (0 + 0)   ...   (1 + 4) + 5 ≡ 1 + (4 + 5)   ...

And we repeat the process again.

    -- on the third day, we know about associativity of 0, 1, and 2
    (0 + 0) + 0 ≡ 0 + (0 + 0)   ...   (0 + 4) + 5 ≡ 0 + (4 + 5)   ...
    (1 + 0) + 0 ≡ 1 + (0 + 0)   ...   (1 + 4) + 5 ≡ 1 + (4 + 5)   ...
    (2 + 0) + 0 ≡ 2 + (0 + 0)   ...   (2 + 4) + 5 ≡ 2 + (4 + 5)   ...

You've got the hang of it by now.

    -- on the fourth day, we know about associativity of 0, 1, 2, and 3
    (0 + 0) + 0 ≡ 0 + (0 + 0)   ...   (0 + 4) + 5 ≡ 0 + (4 + 5)   ...
    (1 + 0) + 0 ≡ 1 + (0 + 0)   ...   (1 + 4) + 5 ≡ 1 + (4 + 5)   ...
    (2 + 0) + 0 ≡ 2 + (0 + 0)   ...   (2 + 4) + 5 ≡ 2 + (4 + 5)   ...
    (3 + 0) + 0 ≡ 3 + (0 + 0)   ...   (3 + 4) + 5 ≡ 3 + (4 + 5)   ...

The process continues.  On the *m*th day we will know all the
judgements where the first number is less than *m*.

There is also a completely finite approach to generating the same equations,
which is left as an exercise for the reader.

### Exercise `+-assoc-finite`

Write out what is known about associativity on each of the first four
days using a finite story of creation, as
[earlier]({{ site.baseurl }}{% link out/plta/Naturals.md %}#finite-creation).


## Associativity with rewrite

There is more than one way to skin a cat.  Here is a second proof of
associativity of addition in Agda, using `rewrite` rather than chains of
equations.
<pre class="Agda">{% raw %}<a id="+-assoc′"></a><a id="16773" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Properties.md %}{% raw %}#16773" class="Function">+-assoc′</a> <a id="16782" class="Symbol">:</a> <a id="16784" class="Symbol">∀</a> <a id="16786" class="Symbol">(</a><a id="16787" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Properties.md %}{% raw %}#16787" class="Bound">m</a> <a id="16789" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Properties.md %}{% raw %}#16789" class="Bound">n</a> <a id="16791" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Properties.md %}{% raw %}#16791" class="Bound">p</a> <a id="16793" class="Symbol">:</a> <a id="16795" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="16796" class="Symbol">)</a> <a id="16798" class="Symbol">→</a> <a id="16800" class="Symbol">(</a><a id="16801" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Properties.md %}{% raw %}#16787" class="Bound">m</a> <a id="16803" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="16805" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Properties.md %}{% raw %}#16789" class="Bound">n</a><a id="16806" class="Symbol">)</a> <a id="16808" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="16810" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Properties.md %}{% raw %}#16791" class="Bound">p</a> <a id="16812" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator">≡</a> <a id="16814" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Properties.md %}{% raw %}#16787" class="Bound">m</a> <a id="16816" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="16818" class="Symbol">(</a><a id="16819" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Properties.md %}{% raw %}#16789" class="Bound">n</a> <a id="16821" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="16823" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Properties.md %}{% raw %}#16791" class="Bound">p</a><a id="16824" class="Symbol">)</a>
<a id="16826" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Properties.md %}{% raw %}#16773" class="Function">+-assoc′</a> <a id="16835" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a> <a id="16840" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Properties.md %}{% raw %}#16840" class="Bound">n</a> <a id="16842" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Properties.md %}{% raw %}#16842" class="Bound">p</a> <a id="16844" class="Symbol">=</a> <a id="16846" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor">refl</a>
<a id="16851" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Properties.md %}{% raw %}#16773" class="Function">+-assoc′</a> <a id="16860" class="Symbol">(</a><a id="16861" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="16865" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Properties.md %}{% raw %}#16865" class="Bound">m</a><a id="16866" class="Symbol">)</a> <a id="16868" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Properties.md %}{% raw %}#16868" class="Bound">n</a> <a id="16870" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Properties.md %}{% raw %}#16870" class="Bound">p</a> <a id="16872" class="Keyword">rewrite</a> <a id="16880" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Properties.md %}{% raw %}#16773" class="Function">+-assoc′</a> <a id="16889" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Properties.md %}{% raw %}#16865" class="Bound">m</a> <a id="16891" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Properties.md %}{% raw %}#16868" class="Bound">n</a> <a id="16893" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Properties.md %}{% raw %}#16870" class="Bound">p</a> <a id="16895" class="Symbol">=</a> <a id="16897" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor">refl</a>{% endraw %}</pre>

For the base case, we must show:

    (zero + n) + p ≡ zero + (n + p)

Simplifying both sides with the base case of addition yields the equation:

    n + p ≡ n + p

This holds trivially. The proof that a term is equal to itself is written `refl`.

For the inductive case, we must show:

    (suc m + n) + p ≡ suc m + (n + p)

Simplifying both sides with the inductive case of addition yields the equation:

    suc ((m + n) + p) ≡ suc (m + (n + p))

After rewriting with the inductive hypothesis these two terms are equal, and the
proof is again given by `refl`.  Rewriting by a given equation is indicated by
the keyword `rewrite` followed by a proof of that equation.  Rewriting avoids
not only chains of equations but also the need to invoke `cong`.


## Commutativity with rewrite

Here is a second proof of commutativity of addition, using `rewrite` rather than
chains of equations.
<pre class="Agda">{% raw %}<a id="+-identity′"></a><a id="17816" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Properties.md %}{% raw %}#17816" class="Function">+-identity′</a> <a id="17828" class="Symbol">:</a> <a id="17830" class="Symbol">∀</a> <a id="17832" class="Symbol">(</a><a id="17833" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Properties.md %}{% raw %}#17833" class="Bound">n</a> <a id="17835" class="Symbol">:</a> <a id="17837" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="17838" class="Symbol">)</a> <a id="17840" class="Symbol">→</a> <a id="17842" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Properties.md %}{% raw %}#17833" class="Bound">n</a> <a id="17844" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="17846" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a> <a id="17851" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator">≡</a> <a id="17853" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Properties.md %}{% raw %}#17833" class="Bound">n</a>
<a id="17855" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Properties.md %}{% raw %}#17816" class="Function">+-identity′</a> <a id="17867" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a> <a id="17872" class="Symbol">=</a> <a id="17874" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor">refl</a>
<a id="17879" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Properties.md %}{% raw %}#17816" class="Function">+-identity′</a> <a id="17891" class="Symbol">(</a><a id="17892" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="17896" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Properties.md %}{% raw %}#17896" class="Bound">n</a><a id="17897" class="Symbol">)</a> <a id="17899" class="Keyword">rewrite</a> <a id="17907" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Properties.md %}{% raw %}#17816" class="Function">+-identity′</a> <a id="17919" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Properties.md %}{% raw %}#17896" class="Bound">n</a> <a id="17921" class="Symbol">=</a> <a id="17923" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor">refl</a>

<a id="+-suc′"></a><a id="17929" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Properties.md %}{% raw %}#17929" class="Function">+-suc′</a> <a id="17936" class="Symbol">:</a> <a id="17938" class="Symbol">∀</a> <a id="17940" class="Symbol">(</a><a id="17941" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Properties.md %}{% raw %}#17941" class="Bound">m</a> <a id="17943" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Properties.md %}{% raw %}#17943" class="Bound">n</a> <a id="17945" class="Symbol">:</a> <a id="17947" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="17948" class="Symbol">)</a> <a id="17950" class="Symbol">→</a> <a id="17952" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Properties.md %}{% raw %}#17941" class="Bound">m</a> <a id="17954" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="17956" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="17960" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Properties.md %}{% raw %}#17943" class="Bound">n</a> <a id="17962" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator">≡</a> <a id="17964" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="17968" class="Symbol">(</a><a id="17969" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Properties.md %}{% raw %}#17941" class="Bound">m</a> <a id="17971" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="17973" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Properties.md %}{% raw %}#17943" class="Bound">n</a><a id="17974" class="Symbol">)</a>
<a id="17976" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Properties.md %}{% raw %}#17929" class="Function">+-suc′</a> <a id="17983" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a> <a id="17988" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Properties.md %}{% raw %}#17988" class="Bound">n</a> <a id="17990" class="Symbol">=</a> <a id="17992" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor">refl</a>
<a id="17997" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Properties.md %}{% raw %}#17929" class="Function">+-suc′</a> <a id="18004" class="Symbol">(</a><a id="18005" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="18009" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Properties.md %}{% raw %}#18009" class="Bound">m</a><a id="18010" class="Symbol">)</a> <a id="18012" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Properties.md %}{% raw %}#18012" class="Bound">n</a> <a id="18014" class="Keyword">rewrite</a> <a id="18022" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Properties.md %}{% raw %}#17929" class="Function">+-suc′</a> <a id="18029" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Properties.md %}{% raw %}#18009" class="Bound">m</a> <a id="18031" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Properties.md %}{% raw %}#18012" class="Bound">n</a> <a id="18033" class="Symbol">=</a> <a id="18035" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor">refl</a>

<a id="+-comm′"></a><a id="18041" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Properties.md %}{% raw %}#18041" class="Function">+-comm′</a> <a id="18049" class="Symbol">:</a> <a id="18051" class="Symbol">∀</a> <a id="18053" class="Symbol">(</a><a id="18054" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Properties.md %}{% raw %}#18054" class="Bound">m</a> <a id="18056" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Properties.md %}{% raw %}#18056" class="Bound">n</a> <a id="18058" class="Symbol">:</a> <a id="18060" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="18061" class="Symbol">)</a> <a id="18063" class="Symbol">→</a> <a id="18065" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Properties.md %}{% raw %}#18054" class="Bound">m</a> <a id="18067" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="18069" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Properties.md %}{% raw %}#18056" class="Bound">n</a> <a id="18071" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator">≡</a> <a id="18073" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Properties.md %}{% raw %}#18056" class="Bound">n</a> <a id="18075" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="18077" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Properties.md %}{% raw %}#18054" class="Bound">m</a>
<a id="18079" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Properties.md %}{% raw %}#18041" class="Function">+-comm′</a> <a id="18087" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Properties.md %}{% raw %}#18087" class="Bound">m</a> <a id="18089" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a> <a id="18094" class="Keyword">rewrite</a> <a id="18102" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Properties.md %}{% raw %}#17816" class="Function">+-identity′</a> <a id="18114" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Properties.md %}{% raw %}#18087" class="Bound">m</a> <a id="18116" class="Symbol">=</a> <a id="18118" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor">refl</a>
<a id="18123" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Properties.md %}{% raw %}#18041" class="Function">+-comm′</a> <a id="18131" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Properties.md %}{% raw %}#18131" class="Bound">m</a> <a id="18133" class="Symbol">(</a><a id="18134" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="18138" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Properties.md %}{% raw %}#18138" class="Bound">n</a><a id="18139" class="Symbol">)</a> <a id="18141" class="Keyword">rewrite</a> <a id="18149" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Properties.md %}{% raw %}#17929" class="Function">+-suc′</a> <a id="18156" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Properties.md %}{% raw %}#18131" class="Bound">m</a> <a id="18158" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Properties.md %}{% raw %}#18138" class="Bound">n</a> <a id="18160" class="Symbol">|</a> <a id="18162" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Properties.md %}{% raw %}#18041" class="Function">+-comm′</a> <a id="18170" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Properties.md %}{% raw %}#18131" class="Bound">m</a> <a id="18172" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Properties.md %}{% raw %}#18138" class="Bound">n</a> <a id="18174" class="Symbol">=</a> <a id="18176" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor">refl</a>{% endraw %}</pre>
In the final line, rewriting with two equations is
indicated by separating the two proofs of the relevant equations by a
vertical bar; the rewrite on the left is performed before that on the
right.


## Building proofs interactively

It is instructive to see how to build the alternative proof of
associativity using the interactive features of Agda in Emacs.
Begin by typing

    +-assoc′ : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
    +-assoc′ m n p = ?

The question mark indicates that you would like Agda to help with
filling in that part of the code.  If you type `^C ^L` (control-C
followed by control-L), the question mark will be replaced.

    +-assoc′ : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
    +-assoc′ m n p = { }0

The empty braces are called a *hole*, and 0 is a number used for
referring to the hole.  The hole may display highlighted in green.
Emacs will also create a new window at the bottom of the screen
displaying the text

    ?0 : ((m + n) + p) ≡ (m + (n + p))

This indicates that hole 0 is to be filled in with a proof of
the stated judgement.

We wish to prove the proposition by induction on `m`.  Move
the cursor into the hole and type `^C ^C`.  You will be given
the prompt:

    pattern variables to case (empty for split on result):

Typing `m` will cause a split on that variable, resulting
in an update to the code.

    +-assoc′ : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
    +-assoc′ zero n p = { }0
    +-assoc′ (suc m) n p = { }1

There are now two holes, and the window at the bottom tells you what
each is required to prove:

    ?0 : ((zero + n) + p) ≡ (zero + (n + p))
    ?1 : ((suc m + n) + p) ≡ (suc m + (n + p))

Going into hole 0 and typing `^C ^,` will display the text:

    Goal: (n + p) ≡ (n + p)
    ————————————————————————————————————————————————————————————
    p : ℕ
    n : ℕ

This indicates that after simplification the goal for hole 0 is as
stated, and that variables `p` and `n` of the stated types are
available to use in the proof.  The proof of the given goal is
trivial, and going into the goal and typing `^C ^R` will fill it in,
renumbering the remaining hole to 0:

    +-assoc′ : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
    +-assoc′ zero n p = refl
    +-assoc′ (suc m) n p = { }0

Going into the new hole 0 and typing `^C ^,` will display the text:

    Goal: suc ((m + n) + p) ≡ suc (m + (n + p))
    ————————————————————————————————————————————————————————————
    p : ℕ
    n : ℕ
    m : ℕ

Again, this gives the simplified goal and the available variables.
In this case, we need to rewrite by the induction
hypothesis, so let's edit the text accordingly:

    +-assoc′ : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
    +-assoc′ zero n p = refl
    +-assoc′ (suc m) n p rewrite +-assoc′ m n p = { }0

Going into the remaining hole and typing `^C ^,` will display the text:

    Goal: suc (m + (n + p)) ≡ suc (m + (n + p))
    ————————————————————————————————————————————————————————————
    p : ℕ
    n : ℕ
    m : ℕ

The proof of the given goal is trivial, and going into the goal and
typing `^C ^R` will fill it in, completing the proof:

    +-assoc′ : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
    +-assoc′ zero n p = refl
    +-assoc′ (suc m) n p rewrite +-assoc′ m n p = refl


### Exercise (`+-swap`)

Show

    m + (n + p) ≡ n + (m + p)

for all naturals `m`, `n`, and `p`. No induction is needed,
just apply the previous results which show addition
is associative and commutative.  You may need to use
the following function from the standard library:

    sym : ∀ {m n : ℕ} → m ≡ n → n ≡ m

### Exercise (`*-distrib-+`)

Show multiplication distributes over addition, that is,

    (m + n) * p ≡ m * p + n * p

for all naturals `m`, `n`, and `p`.

### Exercise (`*-assoc`)

Show multiplication is associative, that is,

    (m * n) * p ≡ m * (n * p)

for all naturals `m`, `n`, and `p`.

### Exercise (`*-comm`)

Show multiplication is commutative, that is,

    m * n ≡ n * m

for all naturals `m` and `n`.  As with commutativity of addition,
you will need to formulate and prove suitable lemmas.

### Exercise (`0∸n≡0`)

Show

    zero ∸ n ≡ zero

for all naturals `n`. Did your proof require induction?

### Exercise (`∸-+-assoc`)

Show that monus associates with addition, that is,

    m ∸ n ∸ p ≡ m ∸ (n + p)

for all naturals `m`, `n`, and `p`.

## Standard library

Definitions similar to those in this chapter can be found in the standard library.
<pre class="Agda">{% raw %}<a id="22652" class="Keyword">import</a> <a id="22659" href="https://agda.github.io/agda-stdlib/Data.Nat.Properties.html" class="Module">Data.Nat.Properties</a> <a id="22679" class="Keyword">using</a> <a id="22685" class="Symbol">(</a><a id="22686" href="https://agda.github.io/agda-stdlib/Data.Nat.Properties.html#7782" class="Function">+-assoc</a><a id="22693" class="Symbol">;</a> <a id="22695" href="https://agda.github.io/agda-stdlib/Data.Nat.Properties.html#7938" class="Function">+-identityʳ</a><a id="22706" class="Symbol">;</a> <a id="22708" href="https://agda.github.io/agda-stdlib/Data.Nat.Properties.html#7679" class="Function">+-suc</a><a id="22713" class="Symbol">;</a> <a id="22715" href="https://agda.github.io/agda-stdlib/Data.Nat.Properties.html#8115" class="Function">+-comm</a><a id="22721" class="Symbol">)</a>{% endraw %}</pre>

## Unicode

This chapter uses the following unicode.

    ∀  U+2200  FOR ALL (\forall)
    ʳ  U+02B3  MODIFIER LETTER SMALL R (\^r)
    ′  U+2032  PRIME (\')
    ″  U+2033  DOUBLE PRIME (\')
    ‴  U+2034  TRIPLE PRIME (\')
    ⁗  U+2057  QUADRUPLE PRIME (\')

Similar to `\r`, the command `\^r` gives access to a variety of
superscript rightward arrows, and also a superscript letter `r`.
The command `\'` gives access to a range of primes (`′ ″ ‴ ⁗`).
