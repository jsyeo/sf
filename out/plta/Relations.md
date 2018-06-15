---
title     : "Relations: Inductive definition of relations"
layout    : page
permalink : /Relations/
---

<pre class="Agda">{% raw %}<a id="123" class="Keyword">module</a> <a id="130" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}" class="Module">plta.Relations</a> <a id="145" class="Keyword">where</a>{% endraw %}</pre>

After having defined operations such as addition and multiplication,
the next step is to define relations, such as *less than or equal*.

## Imports

<pre class="Agda">{% raw %}<a id="326" class="Keyword">import</a> <a id="333" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html" class="Module">Relation.Binary.PropositionalEquality</a> <a id="371" class="Symbol">as</a> <a id="374" class="Module">Eq</a>
<a id="377" class="Keyword">open</a> <a id="382" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html" class="Module">Eq</a> <a id="385" class="Keyword">using</a> <a id="391" class="Symbol">(</a><a id="392" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator">_≡_</a><a id="395" class="Symbol">;</a> <a id="397" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor">refl</a><a id="401" class="Symbol">;</a> <a id="403" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#1075" class="Function">cong</a><a id="407" class="Symbol">;</a> <a id="409" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.Core.html#560" class="Function">sym</a><a id="412" class="Symbol">)</a>
<a id="414" class="Keyword">open</a> <a id="419" class="Keyword">import</a> <a id="426" href="https://agda.github.io/agda-stdlib/Data.Nat.html" class="Module">Data.Nat</a> <a id="435" class="Keyword">using</a> <a id="441" class="Symbol">(</a><a id="442" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="443" class="Symbol">;</a> <a id="445" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a><a id="449" class="Symbol">;</a> <a id="451" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a><a id="454" class="Symbol">;</a> <a id="456" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">_+_</a><a id="459" class="Symbol">;</a> <a id="461" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#433" class="Primitive Operator">_*_</a><a id="464" class="Symbol">;</a> <a id="466" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#320" class="Primitive Operator">_∸_</a><a id="469" class="Symbol">)</a>
<a id="471" class="Keyword">open</a> <a id="476" class="Keyword">import</a> <a id="483" href="https://agda.github.io/agda-stdlib/Data.Nat.Properties.html" class="Module">Data.Nat.Properties</a> <a id="503" class="Keyword">using</a> <a id="509" class="Symbol">(</a><a id="510" href="https://agda.github.io/agda-stdlib/Data.Nat.Properties.html#8115" class="Function">+-comm</a><a id="516" class="Symbol">;</a> <a id="518" href="https://agda.github.io/agda-stdlib/Data.Nat.Properties.html#7679" class="Function">+-suc</a><a id="523" class="Symbol">)</a>{% endraw %}</pre>


## Defining relations

The relation *less than or equal* has an infinite number of
instances.  Here are a few of them:

    0 ≤ 0     0 ≤ 1     0 ≤ 2     0 ≤ 3     ...
              1 ≤ 1     1 ≤ 2     1 ≤ 3     ...
                        2 ≤ 2     2 ≤ 3     ...
                                  3 ≤ 3     ...
                                            ...

And yet, we can write a finite definition that encompasses
all of these instances in just a few lines.  Here is the
definition as a pair of inference rules:

    z≤n --------
        zero ≤ n

        m ≤ n
    s≤s -------------
        suc m ≤ suc n

And here is the definition in Agda:
<pre class="Agda">{% raw %}<a id="1200" class="Keyword">data</a> <a id="_≤_"></a><a id="1205" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#1205" class="Datatype Operator">_≤_</a> <a id="1209" class="Symbol">:</a> <a id="1211" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a> <a id="1213" class="Symbol">→</a> <a id="1215" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a> <a id="1217" class="Symbol">→</a> <a id="1219" class="PrimitiveType">Set</a> <a id="1223" class="Keyword">where</a>
  <a id="_≤_.z≤n"></a><a id="1231" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#1231" class="InductiveConstructor">z≤n</a> <a id="1235" class="Symbol">:</a> <a id="1237" class="Symbol">∀</a> <a id="1239" class="Symbol">{</a><a id="1240" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#1240" class="Bound">m</a> <a id="1242" class="Symbol">:</a> <a id="1244" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="1245" class="Symbol">}</a> <a id="1247" class="Symbol">→</a> <a id="1249" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a> <a id="1254" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#1205" class="Datatype Operator">≤</a> <a id="1256" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#1240" class="Bound">m</a>
  <a id="_≤_.s≤s"></a><a id="1260" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#1260" class="InductiveConstructor">s≤s</a> <a id="1264" class="Symbol">:</a> <a id="1266" class="Symbol">∀</a> <a id="1268" class="Symbol">{</a><a id="1269" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#1269" class="Bound">m</a> <a id="1271" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#1271" class="Bound">n</a> <a id="1273" class="Symbol">:</a> <a id="1275" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="1276" class="Symbol">}</a> <a id="1278" class="Symbol">→</a> <a id="1280" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#1269" class="Bound">m</a> <a id="1282" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#1205" class="Datatype Operator">≤</a> <a id="1284" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#1271" class="Bound">n</a> <a id="1286" class="Symbol">→</a> <a id="1288" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="1292" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#1269" class="Bound">m</a> <a id="1294" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#1205" class="Datatype Operator">≤</a> <a id="1296" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="1300" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#1271" class="Bound">n</a>{% endraw %}</pre>
Here `z≤n` and `s≤s` (with no spaces) are constructor names,
while `zero ≤ m`, and `m ≤ n` and `suc m ≤ suc n` (with spaces)
are types.  This is our first use of an *indexed* datatype,
where we say the type `m ≤ n` is indexed by two naturals, `m` and `n`.

Both definitions above tell us the same two things:

+ *Base case*: for all naturals `n`, the proposition `zero ≤ n` holds
+ *Inductive case*: for all naturals `m` and `n`, if the proposition
  `m ≤ n` holds, then the proposition `suc m ≤ suc n` holds.

In fact, they each give us a bit more detail:

+ *Base case*: for all naturals `n`, the constructor `z≤n`
  produces evidence that `zero ≤ n` holds.
+ *Inductive case*: for all naturals `m` and `n`, the constructor
  `s≤s` takes evidence that `m ≤ n` holds into evidence that
  `suc m ≤ suc n` holds.

For example, here in inference rule notation is the proof that
`2 ≤ 4`.

      z≤n -----
          0 ≤ 2
     s≤s -------
          1 ≤ 3
    s≤s ---------
          2 ≤ 4

And here is the corresponding Agda proof.
<pre class="Agda">{% raw %}<a id="2354" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#2354" class="Function">_</a> <a id="2356" class="Symbol">:</a> <a id="2358" class="Number">2</a> <a id="2360" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#1205" class="Datatype Operator">≤</a> <a id="2362" class="Number">4</a>
<a id="2364" class="Symbol">_</a> <a id="2366" class="Symbol">=</a> <a id="2368" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#1260" class="InductiveConstructor">s≤s</a> <a id="2372" class="Symbol">(</a><a id="2373" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#1260" class="InductiveConstructor">s≤s</a> <a id="2377" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#1231" class="InductiveConstructor">z≤n</a><a id="2380" class="Symbol">)</a>{% endraw %}</pre>


## Implicit arguments

This is our first use of implicit arguments.
In the definition of inequality, the two lines defining the constructors
use `∀`, very similar to our use of `∀` in propositions such as:

    +-comm : ∀ (m n : ℕ) → m + n ≡ n + m

However, here the declarations are surrounded by curly braces `{ }` rather than
parentheses `( )`.  This means that the arguments are *implicit* and need not be
written explicitly; instead, they are *inferred* by Agda's typechecker. Thus, we
write `+-comm m n` for the proof that `m + n ≡ n + m`, but `z≤n` for the proof
that `zero ≤ m`, leaving `m` implicit.  Similarly, if `m≤n` is evidence that
`m ≤ n`, we write write `s≤s m≤n` for evidence that `suc m ≤ suc n`, leaving
both `m` and `n` implicit.

If we wish, it is possible to provide implicit arguments explicitly by
writing the arguments inside curly braces.  For instance, here is the
Agda proof that `2 ≤ 4` repeated, with the implicit arguments made
explicit.
<pre class="Agda">{% raw %}<a id="3378" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#3378" class="Function">_</a> <a id="3380" class="Symbol">:</a> <a id="3382" class="Number">2</a> <a id="3384" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#1205" class="Datatype Operator">≤</a> <a id="3386" class="Number">4</a>
<a id="3388" class="Symbol">_</a> <a id="3390" class="Symbol">=</a> <a id="3392" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#1260" class="InductiveConstructor">s≤s</a> <a id="3396" class="Symbol">{</a><a id="3397" class="Number">1</a><a id="3398" class="Symbol">}</a> <a id="3400" class="Symbol">{</a><a id="3401" class="Number">3</a><a id="3402" class="Symbol">}</a> <a id="3404" class="Symbol">(</a><a id="3405" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#1260" class="InductiveConstructor">s≤s</a> <a id="3409" class="Symbol">{</a><a id="3410" class="Number">0</a><a id="3411" class="Symbol">}</a> <a id="3413" class="Symbol">{</a><a id="3414" class="Number">2</a><a id="3415" class="Symbol">}</a> <a id="3417" class="Symbol">(</a><a id="3418" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#1231" class="InductiveConstructor">z≤n</a> <a id="3422" class="Symbol">{</a><a id="3423" class="Number">2</a><a id="3424" class="Symbol">}))</a>{% endraw %}</pre>


## Precedence

We declare the precedence for comparison as follows.
<pre class="Agda">{% raw %}<a id="3522" class="Keyword">infix</a> <a id="3528" class="Number">4</a> <a id="3530" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#1205" class="Datatype Operator">_≤_</a>{% endraw %}</pre>
We set the precedence of `_≤_` at level 4, so it binds less tightly
that `_+_` at level 6 and hence `1 + 2 ≤ 3` parses as `(1 + 2) ≤ 3`.
We write `infix` to indicate that the operator does not associate to
either the left or right, as it makes no sense to parse `1 ≤ 2 ≤ 3` as
either `(1 ≤ 2) ≤ 3` or `1 ≤ (2 ≤ 3)`.


## Decidability

Given two numbers, it is straightforward to compute whether or not the first is
less than or equal to the second.  We don't give the code for doing so here, but
will return to this point in Chapter [Decidable]({{ site.baseurl }}{% link out/plta/Decidable.md %}).


## Properties of ordering relations

Relations occur all the time, and mathematicians have agreed
on names for some of the most common properties.

+ *Reflexive* For all `n`, the relation `n ≤ n` holds.
+ *Transitive* For all `m`, `n`, and `p`, if `m ≤ n` and
`n ≤ p` hold, then `m ≤ p` holds.
+ *Anti-symmetric* For all `m` and `n`, if both `m ≤ n` and
`n ≤ m` hold, then `m ≡ n` holds.
+ *Total* For all `m` and `n`, either `m ≤ n` or `n ≤ m`
holds.

The relation `_≤_` satisfies all four of these properties.

There are also names for some combinations of these properties.

+ *Preorder* Any relation that is reflexive and transitive.
+ *Partial order* Any preorder that is also anti-symmetric.
+ *Total order* Any partial order that is also total.

If you ever bump into a relation at a party, you now know how
to make small talk, by asking it whether it is reflexive, transitive,
anti-symmetric, and total. Or instead you might ask whether it is a
preorder, partial order, or total order.

Less frivolously, if you ever bump into a relation while reading
a technical paper, this gives you an easy way to orient yourself,
by checking whether or not it is a preorder, partial order, or total order.
A careful author will often make it explicit, for instance by saying
that a given relation is a preorder but not a partial order, or a
partial order but not a total order. (Can you think of examples of
such relations?)


## Reflexivity

The first property to prove about comparison is that it is reflexive:
for any natural `n`, the relation `n ≤ n` holds.
<pre class="Agda">{% raw %}<a id="≤-refl"></a><a id="5716" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#5716" class="Function">≤-refl</a> <a id="5723" class="Symbol">:</a> <a id="5725" class="Symbol">∀</a> <a id="5727" class="Symbol">{</a><a id="5728" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#5728" class="Bound">n</a> <a id="5730" class="Symbol">:</a> <a id="5732" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="5733" class="Symbol">}</a> <a id="5735" class="Symbol">→</a> <a id="5737" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#5728" class="Bound">n</a> <a id="5739" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#1205" class="Datatype Operator">≤</a> <a id="5741" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#5728" class="Bound">n</a>
<a id="5743" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#5716" class="Function">≤-refl</a> <a id="5750" class="Symbol">{</a><a id="5751" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a><a id="5755" class="Symbol">}</a> <a id="5757" class="Symbol">=</a> <a id="5759" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#1231" class="InductiveConstructor">z≤n</a>
<a id="5763" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#5716" class="Function">≤-refl</a> <a id="5770" class="Symbol">{</a><a id="5771" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="5775" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#5775" class="Bound">n</a><a id="5776" class="Symbol">}</a> <a id="5778" class="Symbol">=</a> <a id="5780" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#1260" class="InductiveConstructor">s≤s</a> <a id="5784" class="Symbol">(</a><a id="5785" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#5716" class="Function">≤-refl</a> <a id="5792" class="Symbol">{</a><a id="5793" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#5775" class="Bound">n</a><a id="5794" class="Symbol">})</a>{% endraw %}</pre>
The proof is a straightforward induction on `n`.  In the base case,
`zero ≤ zero` holds by `z≤n`.  In the inductive case, the inductive
hypothesis `≤-refl n` gives us a proof of `n ≤ n`, and applying `s≤s`
to that yields a proof of `suc n ≤ suc n`.

It is a good exercise to prove reflexivity interactively in Emacs,
using holes and the `^C ^C`, `^C ^,`, and `^C ^R` commands.


## Transitivity

The second property to prove about comparison is that it is
transitive: for any naturals `m`, `n`, and `p`, if `m ≤ n` and `n ≤
p` hold, then `m ≤ p` holds.
<pre class="Agda">{% raw %}<a id="≤-trans"></a><a id="6374" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#6374" class="Function">≤-trans</a> <a id="6382" class="Symbol">:</a> <a id="6384" class="Symbol">∀</a> <a id="6386" class="Symbol">{</a><a id="6387" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#6387" class="Bound">m</a> <a id="6389" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#6389" class="Bound">n</a> <a id="6391" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#6391" class="Bound">p</a> <a id="6393" class="Symbol">:</a> <a id="6395" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="6396" class="Symbol">}</a> <a id="6398" class="Symbol">→</a> <a id="6400" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#6387" class="Bound">m</a> <a id="6402" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#1205" class="Datatype Operator">≤</a> <a id="6404" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#6389" class="Bound">n</a> <a id="6406" class="Symbol">→</a> <a id="6408" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#6389" class="Bound">n</a> <a id="6410" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#1205" class="Datatype Operator">≤</a> <a id="6412" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#6391" class="Bound">p</a> <a id="6414" class="Symbol">→</a> <a id="6416" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#6387" class="Bound">m</a> <a id="6418" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#1205" class="Datatype Operator">≤</a> <a id="6420" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#6391" class="Bound">p</a>
<a id="6422" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#6374" class="Function">≤-trans</a> <a id="6430" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#1231" class="InductiveConstructor">z≤n</a> <a id="6434" class="Symbol">_</a> <a id="6436" class="Symbol">=</a> <a id="6438" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#1231" class="InductiveConstructor">z≤n</a>
<a id="6442" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#6374" class="Function">≤-trans</a> <a id="6450" class="Symbol">(</a><a id="6451" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#1260" class="InductiveConstructor">s≤s</a> <a id="6455" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#6455" class="Bound">m≤n</a><a id="6458" class="Symbol">)</a> <a id="6460" class="Symbol">(</a><a id="6461" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#1260" class="InductiveConstructor">s≤s</a> <a id="6465" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#6465" class="Bound">n≤p</a><a id="6468" class="Symbol">)</a> <a id="6470" class="Symbol">=</a> <a id="6472" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#1260" class="InductiveConstructor">s≤s</a> <a id="6476" class="Symbol">(</a><a id="6477" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#6374" class="Function">≤-trans</a> <a id="6485" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#6455" class="Bound">m≤n</a> <a id="6489" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#6465" class="Bound">n≤p</a><a id="6492" class="Symbol">)</a>{% endraw %}</pre>
Here the proof is most easily thought of as by induction on the
*evidence* that `m ≤ n`, so we have left `m`, `n`, and `p` implicit.

In the base case, the first inequality holds by `z≤n`, and so
we are given `zero ≤ n` and `n ≤ p` and must show `zero ≤ p`,
which follows immediately by `z≤n`.  In this
case, the fact that `n ≤ p` is irrelevant, and we write `_` as the
pattern to indicate that the corresponding evidence is unused.

In the inductive case, the first inequality holds by `s≤s m≤n`
and the second inequality by `s≤s n≤p`, and so we are given
`suc m ≤ suc n` and `suc n ≤ suc p`, and must show `suc m ≤ suc p`.
The inductive hypothesis `≤-trans m≤n n≤p` establishes
that `m ≤ p`, and our goal follows by applying `s≤s`.

The case `≤-trans (s≤s m≤n) z≤n` cannot arise, since the first
inequality implies the middle value is `suc n` while the second
inequality implies that it is `zero`.  Agda can determine that
such a case cannot arise, and does not require it to be listed.

Alternatively, we could make the implicit parameters explicit.
<pre class="Agda">{% raw %}<a id="≤-trans′"></a><a id="7571" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#7571" class="Function">≤-trans′</a> <a id="7580" class="Symbol">:</a> <a id="7582" class="Symbol">∀</a> <a id="7584" class="Symbol">(</a><a id="7585" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#7585" class="Bound">m</a> <a id="7587" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#7587" class="Bound">n</a> <a id="7589" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#7589" class="Bound">p</a> <a id="7591" class="Symbol">:</a> <a id="7593" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="7594" class="Symbol">)</a> <a id="7596" class="Symbol">→</a> <a id="7598" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#7585" class="Bound">m</a> <a id="7600" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#1205" class="Datatype Operator">≤</a> <a id="7602" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#7587" class="Bound">n</a> <a id="7604" class="Symbol">→</a> <a id="7606" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#7587" class="Bound">n</a> <a id="7608" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#1205" class="Datatype Operator">≤</a> <a id="7610" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#7589" class="Bound">p</a> <a id="7612" class="Symbol">→</a> <a id="7614" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#7585" class="Bound">m</a> <a id="7616" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#1205" class="Datatype Operator">≤</a> <a id="7618" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#7589" class="Bound">p</a>
<a id="7620" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#7571" class="Function">≤-trans′</a> <a id="7629" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a> <a id="7634" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#7634" class="Bound">n</a> <a id="7636" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#7636" class="Bound">p</a> <a id="7638" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#1231" class="InductiveConstructor">z≤n</a> <a id="7642" class="Symbol">_</a> <a id="7644" class="Symbol">=</a> <a id="7646" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#1231" class="InductiveConstructor">z≤n</a>
<a id="7650" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#7571" class="Function">≤-trans′</a> <a id="7659" class="Symbol">(</a><a id="7660" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="7664" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#7664" class="Bound">m</a><a id="7665" class="Symbol">)</a> <a id="7667" class="Symbol">(</a><a id="7668" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="7672" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#7672" class="Bound">n</a><a id="7673" class="Symbol">)</a> <a id="7675" class="Symbol">(</a><a id="7676" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="7680" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#7680" class="Bound">p</a><a id="7681" class="Symbol">)</a> <a id="7683" class="Symbol">(</a><a id="7684" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#1260" class="InductiveConstructor">s≤s</a> <a id="7688" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#7688" class="Bound">m≤n</a><a id="7691" class="Symbol">)</a> <a id="7693" class="Symbol">(</a><a id="7694" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#1260" class="InductiveConstructor">s≤s</a> <a id="7698" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#7698" class="Bound">n≤p</a><a id="7701" class="Symbol">)</a> <a id="7703" class="Symbol">=</a> <a id="7705" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#1260" class="InductiveConstructor">s≤s</a> <a id="7709" class="Symbol">(</a><a id="7710" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#7571" class="Function">≤-trans′</a> <a id="7719" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#7664" class="Bound">m</a> <a id="7721" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#7672" class="Bound">n</a> <a id="7723" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#7680" class="Bound">p</a> <a id="7725" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#7688" class="Bound">m≤n</a> <a id="7729" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#7698" class="Bound">n≤p</a><a id="7732" class="Symbol">)</a>{% endraw %}</pre>
One might argue that this is clearer or one might argue that the extra
length obscures the essence of the proof.  We will usually opt for
shorter proofs.

The technique of inducting on evidence that a property holds (e.g.,
inducting on evidence that `m ≤ n`)---rather than induction on the
value of which the property holds (e.g., inducting on `m`)---will turn
out to be immensely valuable, and one that we use often.

Again, it is a good exercise to prove transitivity interactively in Emacs,
using holes and the `^C ^C`, `^C ^,`, and `^C ^R` commands.


## Anti-symmetry

The third property to prove about comparison is that it is antisymmetric:
for all naturals `m` and `n`, if both `m ≤ n` and `n ≤ m` hold, then
`m ≡ n` holds.
<pre class="Agda">{% raw %}<a id="≤-antisym"></a><a id="8490" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#8490" class="Function">≤-antisym</a> <a id="8500" class="Symbol">:</a> <a id="8502" class="Symbol">∀</a> <a id="8504" class="Symbol">{</a><a id="8505" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#8505" class="Bound">m</a> <a id="8507" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#8507" class="Bound">n</a> <a id="8509" class="Symbol">:</a> <a id="8511" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="8512" class="Symbol">}</a> <a id="8514" class="Symbol">→</a> <a id="8516" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#8505" class="Bound">m</a> <a id="8518" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#1205" class="Datatype Operator">≤</a> <a id="8520" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#8507" class="Bound">n</a> <a id="8522" class="Symbol">→</a> <a id="8524" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#8507" class="Bound">n</a> <a id="8526" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#1205" class="Datatype Operator">≤</a> <a id="8528" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#8505" class="Bound">m</a> <a id="8530" class="Symbol">→</a> <a id="8532" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#8505" class="Bound">m</a> <a id="8534" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator">≡</a> <a id="8536" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#8507" class="Bound">n</a>
<a id="8538" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#8490" class="Function">≤-antisym</a> <a id="8548" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#1231" class="InductiveConstructor">z≤n</a> <a id="8552" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#1231" class="InductiveConstructor">z≤n</a> <a id="8556" class="Symbol">=</a> <a id="8558" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor">refl</a>
<a id="8563" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#8490" class="Function">≤-antisym</a> <a id="8573" class="Symbol">(</a><a id="8574" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#1260" class="InductiveConstructor">s≤s</a> <a id="8578" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#8578" class="Bound">m≤n</a><a id="8581" class="Symbol">)</a> <a id="8583" class="Symbol">(</a><a id="8584" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#1260" class="InductiveConstructor">s≤s</a> <a id="8588" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#8588" class="Bound">n≤m</a><a id="8591" class="Symbol">)</a> <a id="8593" class="Symbol">=</a> <a id="8595" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#1075" class="Function">cong</a> <a id="8600" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="8604" class="Symbol">(</a><a id="8605" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#8490" class="Function">≤-antisym</a> <a id="8615" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#8578" class="Bound">m≤n</a> <a id="8619" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#8588" class="Bound">n≤m</a><a id="8622" class="Symbol">)</a>{% endraw %}</pre>
Again, the proof is by induction over the evidence that `m ≤ n`
and `n ≤ m` hold, and so we have left `m` and `n` implicit.

In the base case, both inequalities hold by `z≤n`,
and so we are given `zero ≤ zero` and `zero ≤ zero` and must
show `zero ≡ zero`, which follows by reflexivity.  (Reflexivity
of equality, that is, not reflexivity of inequality.)

In the inductive case, the first inequality holds by `s≤s m≤n`
and the second inequality holds by `s≤s n≤m`, and so we are
given `suc m ≤ suc n` and `suc n ≤ suc m` and must show `suc m ≡ suc n`.
The inductive hypothesis `≤-antisym m≤n n≤m` establishes that `m ≡ n`,
and our goal follows by congruence.

### Exercise (≤-antisym-cases)

The above proof omits cases where one argument is `z≤n` and one
argument is `s≤s`.  Why is it ok to omit them?


## Total

The fourth property to prove about comparison is that it is total:
for any naturals `m` and `n` either `m ≤ n` or `n ≤ m`, or both if
`m` and `n` are equal.

We specify what it means for inequality to be total.
<pre class="Agda">{% raw %}<a id="9674" class="Keyword">data</a> <a id="Total"></a><a id="9679" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#9679" class="Datatype">Total</a> <a id="9685" class="Symbol">(</a><a id="9686" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#9686" class="Bound">m</a> <a id="9688" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#9688" class="Bound">n</a> <a id="9690" class="Symbol">:</a> <a id="9692" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="9693" class="Symbol">)</a> <a id="9695" class="Symbol">:</a> <a id="9697" class="PrimitiveType">Set</a> <a id="9701" class="Keyword">where</a>
  <a id="Total.forward"></a><a id="9709" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#9709" class="InductiveConstructor">forward</a> <a id="9717" class="Symbol">:</a> <a id="9719" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#9686" class="Bound">m</a> <a id="9721" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#1205" class="Datatype Operator">≤</a> <a id="9723" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#9688" class="Bound">n</a> <a id="9725" class="Symbol">→</a> <a id="9727" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#9679" class="Datatype">Total</a> <a id="9733" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#9686" class="Bound">m</a> <a id="9735" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#9688" class="Bound">n</a>
  <a id="Total.flipped"></a><a id="9739" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#9739" class="InductiveConstructor">flipped</a> <a id="9747" class="Symbol">:</a> <a id="9749" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#9688" class="Bound">n</a> <a id="9751" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#1205" class="Datatype Operator">≤</a> <a id="9753" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#9686" class="Bound">m</a> <a id="9755" class="Symbol">→</a> <a id="9757" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#9679" class="Datatype">Total</a> <a id="9763" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#9686" class="Bound">m</a> <a id="9765" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#9688" class="Bound">n</a>{% endraw %}</pre>
Evidence that `Total m n` holds is either of the form
`forward m≤n` or `flipped n≤m`, where `m≤n` and `n≤m` are
evidence of `m ≤ n` and `n ≤ m` respectively.

This is our first use of a datatype with *parameters*,
in this case `m` and `n`.  It is equivalent to the following
indexed datatype.
<pre class="Agda">{% raw %}<a id="10084" class="Keyword">data</a> <a id="Total′"></a><a id="10089" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#10089" class="Datatype">Total′</a> <a id="10096" class="Symbol">:</a> <a id="10098" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a> <a id="10100" class="Symbol">→</a> <a id="10102" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a> <a id="10104" class="Symbol">→</a> <a id="10106" class="PrimitiveType">Set</a> <a id="10110" class="Keyword">where</a>
  <a id="Total′.forward′"></a><a id="10118" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#10118" class="InductiveConstructor">forward′</a> <a id="10127" class="Symbol">:</a> <a id="10129" class="Symbol">∀</a> <a id="10131" class="Symbol">{</a><a id="10132" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#10132" class="Bound">m</a> <a id="10134" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#10134" class="Bound">n</a> <a id="10136" class="Symbol">:</a> <a id="10138" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="10139" class="Symbol">}</a> <a id="10141" class="Symbol">→</a> <a id="10143" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#10132" class="Bound">m</a> <a id="10145" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#1205" class="Datatype Operator">≤</a> <a id="10147" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#10134" class="Bound">n</a> <a id="10149" class="Symbol">→</a> <a id="10151" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#10089" class="Datatype">Total′</a> <a id="10158" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#10132" class="Bound">m</a> <a id="10160" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#10134" class="Bound">n</a>
  <a id="Total′.flipped′"></a><a id="10164" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#10164" class="InductiveConstructor">flipped′</a> <a id="10173" class="Symbol">:</a> <a id="10175" class="Symbol">∀</a> <a id="10177" class="Symbol">{</a><a id="10178" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#10178" class="Bound">m</a> <a id="10180" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#10180" class="Bound">n</a> <a id="10182" class="Symbol">:</a> <a id="10184" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="10185" class="Symbol">}</a> <a id="10187" class="Symbol">→</a> <a id="10189" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#10180" class="Bound">n</a> <a id="10191" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#1205" class="Datatype Operator">≤</a> <a id="10193" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#10178" class="Bound">m</a> <a id="10195" class="Symbol">→</a> <a id="10197" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#10089" class="Datatype">Total′</a> <a id="10204" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#10178" class="Bound">m</a> <a id="10206" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#10180" class="Bound">n</a>{% endraw %}</pre>
Each parameter of the type translates as an implicit
parameter of each constructor.
Unlike an indexed datatype, where the indexes can vary
(as in `zero ≤ n` and `suc m ≤ suc n`), in a parameterised
datatype the parameters must always be the same (as in `Total m n`).
Parameterised declarations are shorter, easier to read, and let Agda
exploit the uniformity of the parameters, so we will use them in
preference to indexed types when possible.

With that preliminary out of the way, we specify and prove totality.
<pre class="Agda">{% raw %}<a id="≤-total"></a><a id="10746" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#10746" class="Function">≤-total</a> <a id="10754" class="Symbol">:</a> <a id="10756" class="Symbol">∀</a> <a id="10758" class="Symbol">(</a><a id="10759" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#10759" class="Bound">m</a> <a id="10761" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#10761" class="Bound">n</a> <a id="10763" class="Symbol">:</a> <a id="10765" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="10766" class="Symbol">)</a> <a id="10768" class="Symbol">→</a> <a id="10770" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#9679" class="Datatype">Total</a> <a id="10776" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#10759" class="Bound">m</a> <a id="10778" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#10761" class="Bound">n</a>
<a id="10780" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#10746" class="Function">≤-total</a> <a id="10788" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a>    <a id="10796" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#10796" class="Bound">n</a>                         <a id="10822" class="Symbol">=</a>  <a id="10825" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#9709" class="InductiveConstructor">forward</a> <a id="10833" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#1231" class="InductiveConstructor">z≤n</a>
<a id="10837" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#10746" class="Function">≤-total</a> <a id="10845" class="Symbol">(</a><a id="10846" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="10850" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#10850" class="Bound">m</a><a id="10851" class="Symbol">)</a> <a id="10853" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a>                      <a id="10879" class="Symbol">=</a>  <a id="10882" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#9739" class="InductiveConstructor">flipped</a> <a id="10890" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#1231" class="InductiveConstructor">z≤n</a>
<a id="10894" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#10746" class="Function">≤-total</a> <a id="10902" class="Symbol">(</a><a id="10903" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="10907" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#10907" class="Bound">m</a><a id="10908" class="Symbol">)</a> <a id="10910" class="Symbol">(</a><a id="10911" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="10915" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#10915" class="Bound">n</a><a id="10916" class="Symbol">)</a> <a id="10918" class="Keyword">with</a> <a id="10923" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#10746" class="Function">≤-total</a> <a id="10931" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#10907" class="Bound">m</a> <a id="10933" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#10915" class="Bound">n</a>
<a id="10935" class="Symbol">...</a>                        <a id="10962" class="Symbol">|</a> <a id="10964" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#9709" class="InductiveConstructor">forward</a> <a id="10972" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#10972" class="Bound">m≤n</a>  <a id="10977" class="Symbol">=</a>  <a id="10980" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#9709" class="InductiveConstructor">forward</a> <a id="10988" class="Symbol">(</a><a id="10989" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#1260" class="InductiveConstructor">s≤s</a> <a id="10993" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#10972" class="Bound">m≤n</a><a id="10996" class="Symbol">)</a>
<a id="10998" class="Symbol">...</a>                        <a id="11025" class="Symbol">|</a> <a id="11027" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#9739" class="InductiveConstructor">flipped</a> <a id="11035" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#11035" class="Bound">n≤m</a>  <a id="11040" class="Symbol">=</a>  <a id="11043" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#9739" class="InductiveConstructor">flipped</a> <a id="11051" class="Symbol">(</a><a id="11052" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#1260" class="InductiveConstructor">s≤s</a> <a id="11056" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#11035" class="Bound">n≤m</a><a id="11059" class="Symbol">)</a>{% endraw %}</pre>
In this case the proof is by induction over both the first
and second arguments.  We perform a case analysis:

+ *First base case*: If the first argument is `zero` and the
  second argument is `n` then the forward case holds,
  with `z≤n` as evidence that `zero ≤ n`.

+ *Second base case*: If the first argument is `suc m` and the
  second argument is `zero` then the flipped case holds, with
  `z≤n` as evidence that `zero ≤ suc m`.

+ *Inductive case*: If the first argument is `suc m` and the
  second argument is `suc n`, then the inductive hypothesis
  `≤-total m n` establishes one of the following:

  - The forward case of the inductive hypothesis holds with `m≤n` as
    evidence that `m ≤ n`, from which it follows that the forward case of the
    proposition holds with `s≤s m≤n` as evidence that `suc m ≤ suc n`.

  - The flipped case of the inductive hypothesis holds with `n≤m` as
    evidence that `n ≤ m`, from which it follows that the flipped case of the
    proposition holds with `s≤s n≤m` as evidence that `suc n ≤ suc m`.

This is our first use of the `with` clause in Agda.  The keyword
`with` is followed by an expression and one or more subsequent lines.
Each line begins with an ellipsis (`...`) and a vertical bar (`|`),
followed by a pattern to be matched against the expression
and the right-hand side of the equation.

Every use of `with` is equivalent to defining a helper function.  For
example, the definition above is equivalent to the following.
<pre class="Agda">{% raw %}<a id="≤-total′"></a><a id="12567" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#12567" class="Function">≤-total′</a> <a id="12576" class="Symbol">:</a> <a id="12578" class="Symbol">∀</a> <a id="12580" class="Symbol">(</a><a id="12581" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#12581" class="Bound">m</a> <a id="12583" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#12583" class="Bound">n</a> <a id="12585" class="Symbol">:</a> <a id="12587" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="12588" class="Symbol">)</a> <a id="12590" class="Symbol">→</a> <a id="12592" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#9679" class="Datatype">Total</a> <a id="12598" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#12581" class="Bound">m</a> <a id="12600" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#12583" class="Bound">n</a>
<a id="12602" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#12567" class="Function">≤-total′</a> <a id="12611" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a>    <a id="12619" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#12619" class="Bound">n</a>        <a id="12628" class="Symbol">=</a>  <a id="12631" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#9709" class="InductiveConstructor">forward</a> <a id="12639" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#1231" class="InductiveConstructor">z≤n</a>
<a id="12643" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#12567" class="Function">≤-total′</a> <a id="12652" class="Symbol">(</a><a id="12653" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="12657" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#12657" class="Bound">m</a><a id="12658" class="Symbol">)</a> <a id="12660" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a>     <a id="12669" class="Symbol">=</a>  <a id="12672" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#9739" class="InductiveConstructor">flipped</a> <a id="12680" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#1231" class="InductiveConstructor">z≤n</a>
<a id="12684" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#12567" class="Function">≤-total′</a> <a id="12693" class="Symbol">(</a><a id="12694" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="12698" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#12698" class="Bound">m</a><a id="12699" class="Symbol">)</a> <a id="12701" class="Symbol">(</a><a id="12702" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="12706" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#12706" class="Bound">n</a><a id="12707" class="Symbol">)</a>  <a id="12710" class="Symbol">=</a>  <a id="12713" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#12745" class="Function">helper</a> <a id="12720" class="Symbol">(</a><a id="12721" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#12567" class="Function">≤-total′</a> <a id="12730" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#12698" class="Bound">m</a> <a id="12732" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#12706" class="Bound">n</a><a id="12733" class="Symbol">)</a>
  <a id="12737" class="Keyword">where</a>
  <a id="12745" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#12745" class="Function">helper</a> <a id="12752" class="Symbol">:</a> <a id="12754" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#9679" class="Datatype">Total</a> <a id="12760" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#12698" class="Bound">m</a> <a id="12762" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#12706" class="Bound">n</a> <a id="12764" class="Symbol">→</a> <a id="12766" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#9679" class="Datatype">Total</a> <a id="12772" class="Symbol">(</a><a id="12773" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="12777" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#12698" class="Bound">m</a><a id="12778" class="Symbol">)</a> <a id="12780" class="Symbol">(</a><a id="12781" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="12785" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#12706" class="Bound">n</a><a id="12786" class="Symbol">)</a>
  <a id="12790" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#12745" class="Function">helper</a> <a id="12797" class="Symbol">(</a><a id="12798" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#9709" class="InductiveConstructor">forward</a> <a id="12806" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#12806" class="Bound">m≤n</a><a id="12809" class="Symbol">)</a>  <a id="12812" class="Symbol">=</a>  <a id="12815" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#9709" class="InductiveConstructor">forward</a> <a id="12823" class="Symbol">(</a><a id="12824" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#1260" class="InductiveConstructor">s≤s</a> <a id="12828" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#12806" class="Bound">m≤n</a><a id="12831" class="Symbol">)</a>
  <a id="12835" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#12745" class="Function">helper</a> <a id="12842" class="Symbol">(</a><a id="12843" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#9739" class="InductiveConstructor">flipped</a> <a id="12851" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#12851" class="Bound">n≤m</a><a id="12854" class="Symbol">)</a>  <a id="12857" class="Symbol">=</a>  <a id="12860" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#9739" class="InductiveConstructor">flipped</a> <a id="12868" class="Symbol">(</a><a id="12869" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#1260" class="InductiveConstructor">s≤s</a> <a id="12873" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#12851" class="Bound">n≤m</a><a id="12876" class="Symbol">)</a>{% endraw %}</pre>
This is also our first use of a `where` clause in Agda.  The keyword `where` is
followed by one or more definitions, which must be indented.  Any variables
bound of the left-hand side of the preceding equation (in this case, `m` and
`n`) are in scope within the nested definition, and any identifiers bound in the
nested definition (in this case, `helper`) are in scope in the right-hand side
of the preceding equation.

If both arguments are equal, then both cases hold and we could return evidence
of either.  In the code above we return the forward case, but there is a
variant that returns the flipped case.
<pre class="Agda">{% raw %}<a id="≤-total″"></a><a id="13514" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#13514" class="Function">≤-total″</a> <a id="13523" class="Symbol">:</a> <a id="13525" class="Symbol">∀</a> <a id="13527" class="Symbol">(</a><a id="13528" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#13528" class="Bound">m</a> <a id="13530" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#13530" class="Bound">n</a> <a id="13532" class="Symbol">:</a> <a id="13534" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="13535" class="Symbol">)</a> <a id="13537" class="Symbol">→</a> <a id="13539" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#9679" class="Datatype">Total</a> <a id="13545" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#13528" class="Bound">m</a> <a id="13547" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#13530" class="Bound">n</a>
<a id="13549" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#13514" class="Function">≤-total″</a> <a id="13558" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#13558" class="Bound">m</a>       <a id="13566" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a>                      <a id="13592" class="Symbol">=</a>  <a id="13595" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#9739" class="InductiveConstructor">flipped</a> <a id="13603" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#1231" class="InductiveConstructor">z≤n</a>
<a id="13607" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#13514" class="Function">≤-total″</a> <a id="13616" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a>    <a id="13624" class="Symbol">(</a><a id="13625" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="13629" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#13629" class="Bound">n</a><a id="13630" class="Symbol">)</a>                   <a id="13650" class="Symbol">=</a>  <a id="13653" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#9709" class="InductiveConstructor">forward</a> <a id="13661" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#1231" class="InductiveConstructor">z≤n</a>
<a id="13665" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#13514" class="Function">≤-total″</a> <a id="13674" class="Symbol">(</a><a id="13675" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="13679" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#13679" class="Bound">m</a><a id="13680" class="Symbol">)</a> <a id="13682" class="Symbol">(</a><a id="13683" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="13687" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#13687" class="Bound">n</a><a id="13688" class="Symbol">)</a> <a id="13690" class="Keyword">with</a> <a id="13695" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#13514" class="Function">≤-total″</a> <a id="13704" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#13679" class="Bound">m</a> <a id="13706" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#13687" class="Bound">n</a>
<a id="13708" class="Symbol">...</a>                        <a id="13735" class="Symbol">|</a> <a id="13737" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#9709" class="InductiveConstructor">forward</a> <a id="13745" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#13745" class="Bound">m≤n</a>   <a id="13751" class="Symbol">=</a>  <a id="13754" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#9709" class="InductiveConstructor">forward</a> <a id="13762" class="Symbol">(</a><a id="13763" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#1260" class="InductiveConstructor">s≤s</a> <a id="13767" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#13745" class="Bound">m≤n</a><a id="13770" class="Symbol">)</a>
<a id="13772" class="Symbol">...</a>                        <a id="13799" class="Symbol">|</a> <a id="13801" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#9739" class="InductiveConstructor">flipped</a> <a id="13809" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#13809" class="Bound">n≤m</a>   <a id="13815" class="Symbol">=</a>  <a id="13818" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#9739" class="InductiveConstructor">flipped</a> <a id="13826" class="Symbol">(</a><a id="13827" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#1260" class="InductiveConstructor">s≤s</a> <a id="13831" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#13809" class="Bound">n≤m</a><a id="13834" class="Symbol">)</a>{% endraw %}</pre>
It differs from the original code in that it pattern
matches on the second argument before the first argument.


## Monotonicity

If one bumps into both an operator and an ordering at a party, one may ask if
the operator is *monotonic* with regard to the ordering.  For example, addition
is monotonic with regard to inequality, meaning

    ∀ {m n p q : ℕ} → m ≤ n → p ≤ q → m + p ≤ n + q

The proof is straightforward using the techniques we have learned, and is best
broken into three parts. First, we deal with the special case of showing
addition is monotonic on the right.
<pre class="Agda">{% raw %}<a id="+-monoʳ-≤"></a><a id="14438" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#14438" class="Function">+-monoʳ-≤</a> <a id="14448" class="Symbol">:</a> <a id="14450" class="Symbol">∀</a> <a id="14452" class="Symbol">(</a><a id="14453" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#14453" class="Bound">m</a> <a id="14455" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#14455" class="Bound">p</a> <a id="14457" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#14457" class="Bound">q</a> <a id="14459" class="Symbol">:</a> <a id="14461" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="14462" class="Symbol">)</a> <a id="14464" class="Symbol">→</a> <a id="14466" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#14455" class="Bound">p</a> <a id="14468" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#1205" class="Datatype Operator">≤</a> <a id="14470" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#14457" class="Bound">q</a> <a id="14472" class="Symbol">→</a> <a id="14474" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#14453" class="Bound">m</a> <a id="14476" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="14478" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#14455" class="Bound">p</a> <a id="14480" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#1205" class="Datatype Operator">≤</a> <a id="14482" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#14453" class="Bound">m</a> <a id="14484" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="14486" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#14457" class="Bound">q</a>
<a id="14488" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#14438" class="Function">+-monoʳ-≤</a> <a id="14498" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a>    <a id="14506" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#14506" class="Bound">p</a> <a id="14508" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#14508" class="Bound">q</a> <a id="14510" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#14510" class="Bound">p≤q</a>  <a id="14515" class="Symbol">=</a>  <a id="14518" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#14510" class="Bound">p≤q</a>
<a id="14522" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#14438" class="Function">+-monoʳ-≤</a> <a id="14532" class="Symbol">(</a><a id="14533" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="14537" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#14537" class="Bound">m</a><a id="14538" class="Symbol">)</a> <a id="14540" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#14540" class="Bound">p</a> <a id="14542" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#14542" class="Bound">q</a> <a id="14544" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#14544" class="Bound">p≤q</a>  <a id="14549" class="Symbol">=</a>  <a id="14552" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#1260" class="InductiveConstructor">s≤s</a> <a id="14556" class="Symbol">(</a><a id="14557" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#14438" class="Function">+-monoʳ-≤</a> <a id="14567" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#14537" class="Bound">m</a> <a id="14569" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#14540" class="Bound">p</a> <a id="14571" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#14542" class="Bound">q</a> <a id="14573" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#14544" class="Bound">p≤q</a><a id="14576" class="Symbol">)</a>{% endraw %}</pre>
The proof is by induction on the first argument.

+ *Base case*: The first argument is `zero` in which case
  `zero + p ≤ zero + q` simplifies to `p ≤ q`, the evidence
  for which is given by the argument `p≤q`.

+ *Inductive case*: The first argument is `suc m`, in which case
  `suc m + p ≤ suc m + q` simplifies to `suc (m + p) ≤ suc (m + q)`.
  The inductive hypothesis `+-monoʳ-≤ m p q p≤q` establishes that
  `m + p ≤ m + q`, and our goal follows by applying `s≤s`.

Second, we deal with the special case of showing addition is
monotonic on the left. This follows from the previous
result and the commutativity of addition.
<pre class="Agda">{% raw %}<a id="+-monoˡ-≤"></a><a id="15232" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#15232" class="Function">+-monoˡ-≤</a> <a id="15242" class="Symbol">:</a> <a id="15244" class="Symbol">∀</a> <a id="15246" class="Symbol">(</a><a id="15247" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#15247" class="Bound">m</a> <a id="15249" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#15249" class="Bound">n</a> <a id="15251" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#15251" class="Bound">p</a> <a id="15253" class="Symbol">:</a> <a id="15255" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="15256" class="Symbol">)</a> <a id="15258" class="Symbol">→</a> <a id="15260" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#15247" class="Bound">m</a> <a id="15262" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#1205" class="Datatype Operator">≤</a> <a id="15264" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#15249" class="Bound">n</a> <a id="15266" class="Symbol">→</a> <a id="15268" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#15247" class="Bound">m</a> <a id="15270" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="15272" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#15251" class="Bound">p</a> <a id="15274" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#1205" class="Datatype Operator">≤</a> <a id="15276" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#15249" class="Bound">n</a> <a id="15278" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="15280" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#15251" class="Bound">p</a>
<a id="15282" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#15232" class="Function">+-monoˡ-≤</a> <a id="15292" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#15292" class="Bound">m</a> <a id="15294" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#15294" class="Bound">n</a> <a id="15296" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#15296" class="Bound">p</a> <a id="15298" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#15298" class="Bound">m≤n</a> <a id="15302" class="Keyword">rewrite</a> <a id="15310" href="https://agda.github.io/agda-stdlib/Data.Nat.Properties.html#8115" class="Function">+-comm</a> <a id="15317" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#15292" class="Bound">m</a> <a id="15319" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#15296" class="Bound">p</a> <a id="15321" class="Symbol">|</a> <a id="15323" href="https://agda.github.io/agda-stdlib/Data.Nat.Properties.html#8115" class="Function">+-comm</a> <a id="15330" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#15294" class="Bound">n</a> <a id="15332" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#15296" class="Bound">p</a> <a id="15334" class="Symbol">=</a> <a id="15336" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#14438" class="Function">+-monoʳ-≤</a> <a id="15346" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#15296" class="Bound">p</a> <a id="15348" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#15292" class="Bound">m</a> <a id="15350" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#15294" class="Bound">n</a> <a id="15352" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#15298" class="Bound">m≤n</a>{% endraw %}</pre>
Rewriting by `+-comm m p` and `+-comm n p` converts `m + p ≤ n + p` into
`p + m ≤ p + n`, which is proved by invoking `+-monoʳ-≤ p m n m≤n`.

Third, we combine the two previous results.
<pre class="Agda">{% raw %}<a id="+-mono-≤"></a><a id="15566" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#15566" class="Function">+-mono-≤</a> <a id="15575" class="Symbol">:</a> <a id="15577" class="Symbol">∀</a> <a id="15579" class="Symbol">(</a><a id="15580" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#15580" class="Bound">m</a> <a id="15582" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#15582" class="Bound">n</a> <a id="15584" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#15584" class="Bound">p</a> <a id="15586" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#15586" class="Bound">q</a> <a id="15588" class="Symbol">:</a> <a id="15590" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="15591" class="Symbol">)</a> <a id="15593" class="Symbol">→</a> <a id="15595" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#15580" class="Bound">m</a> <a id="15597" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#1205" class="Datatype Operator">≤</a> <a id="15599" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#15582" class="Bound">n</a> <a id="15601" class="Symbol">→</a> <a id="15603" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#15584" class="Bound">p</a> <a id="15605" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#1205" class="Datatype Operator">≤</a> <a id="15607" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#15586" class="Bound">q</a> <a id="15609" class="Symbol">→</a> <a id="15611" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#15580" class="Bound">m</a> <a id="15613" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="15615" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#15584" class="Bound">p</a> <a id="15617" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#1205" class="Datatype Operator">≤</a> <a id="15619" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#15582" class="Bound">n</a> <a id="15621" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="15623" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#15586" class="Bound">q</a>
<a id="15625" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#15566" class="Function">+-mono-≤</a> <a id="15634" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#15634" class="Bound">m</a> <a id="15636" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#15636" class="Bound">n</a> <a id="15638" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#15638" class="Bound">p</a> <a id="15640" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#15640" class="Bound">q</a> <a id="15642" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#15642" class="Bound">m≤n</a> <a id="15646" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#15646" class="Bound">p≤q</a> <a id="15650" class="Symbol">=</a> <a id="15652" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#6374" class="Function">≤-trans</a> <a id="15660" class="Symbol">(</a><a id="15661" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#15232" class="Function">+-monoˡ-≤</a> <a id="15671" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#15634" class="Bound">m</a> <a id="15673" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#15636" class="Bound">n</a> <a id="15675" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#15638" class="Bound">p</a> <a id="15677" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#15642" class="Bound">m≤n</a><a id="15680" class="Symbol">)</a> <a id="15682" class="Symbol">(</a><a id="15683" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#14438" class="Function">+-monoʳ-≤</a> <a id="15693" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#15636" class="Bound">n</a> <a id="15695" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#15638" class="Bound">p</a> <a id="15697" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#15640" class="Bound">q</a> <a id="15699" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#15646" class="Bound">p≤q</a><a id="15702" class="Symbol">)</a>{% endraw %}</pre>
Invoking `+-monoˡ-≤ m n p m≤n` proves `m + p ≤ n + p` and invoking
`+-monoʳ-≤ n p q p≤q` proves `n + p ≤ n + q`, and combining these with
transitivity proves `m + p ≤ n + q`, as was to be shown.

### Exercise (stretch, `≤-reasoning`)

The proof of monotonicity (and the associated lemmas) can be written
in a more readable form by using an anologue of our notation for
`≡-reasoning`.  Read ahead to chapter [Equality]({{ site.baseurl }}{% link out/plta/Equality.md %}) to
see how `≡-reasoning` is defined, define `≤-reasoning` analogously,
and use it to write out an alternative proof that addition is
monotonic with regard to inequality.


## Strict inequality {#strict-inequality}

We can define strict inequality similarly to inequality.
<pre class="Agda">{% raw %}<a id="16469" class="Keyword">infix</a> <a id="16475" class="Number">4</a> <a id="16477" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#16487" class="Datatype Operator">_&lt;_</a>

<a id="16482" class="Keyword">data</a> <a id="_&lt;_"></a><a id="16487" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#16487" class="Datatype Operator">_&lt;_</a> <a id="16491" class="Symbol">:</a> <a id="16493" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a> <a id="16495" class="Symbol">→</a> <a id="16497" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a> <a id="16499" class="Symbol">→</a> <a id="16501" class="PrimitiveType">Set</a> <a id="16505" class="Keyword">where</a>
  <a id="_&lt;_.z&lt;s"></a><a id="16513" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#16513" class="InductiveConstructor">z&lt;s</a> <a id="16517" class="Symbol">:</a> <a id="16519" class="Symbol">∀</a> <a id="16521" class="Symbol">{</a><a id="16522" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#16522" class="Bound">n</a> <a id="16524" class="Symbol">:</a> <a id="16526" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="16527" class="Symbol">}</a> <a id="16529" class="Symbol">→</a> <a id="16531" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a> <a id="16536" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#16487" class="Datatype Operator">&lt;</a> <a id="16538" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="16542" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#16522" class="Bound">n</a>
  <a id="_&lt;_.s&lt;s"></a><a id="16546" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#16546" class="InductiveConstructor">s&lt;s</a> <a id="16550" class="Symbol">:</a> <a id="16552" class="Symbol">∀</a> <a id="16554" class="Symbol">{</a><a id="16555" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#16555" class="Bound">m</a> <a id="16557" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#16557" class="Bound">n</a> <a id="16559" class="Symbol">:</a> <a id="16561" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="16562" class="Symbol">}</a> <a id="16564" class="Symbol">→</a> <a id="16566" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#16555" class="Bound">m</a> <a id="16568" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#16487" class="Datatype Operator">&lt;</a> <a id="16570" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#16557" class="Bound">n</a> <a id="16572" class="Symbol">→</a> <a id="16574" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="16578" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#16555" class="Bound">m</a> <a id="16580" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#16487" class="Datatype Operator">&lt;</a> <a id="16582" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="16586" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#16557" class="Bound">n</a>{% endraw %}</pre>
The key difference is that zero is less than the successor of an
arbitrary number, but is not less than zero.

Clearly, strict inequality is not reflexive. However it is
*irreflexive* in that `n < n` never holds for any value of `n`.
Like inequality, strict inequality is transitive.
Strict inequality is not total, but satisfies the closely related property of
*trichotomy*: for any `m` and `n`, exactly one of `m < n`, `m ≡ n`, or `m > n`
holds (where we define `m > n` to hold exactly where `n < m`).
It is also monotonic with regards to addition and multiplication.

Most of the above are considered in exercises below.  Irreflexivity
requires negation, as does the fact that the three cases in
trichotomy are mutually exclusive, so those points are deferred
to the chapter that introduces [negation]({{ site.baseurl }}{% link out/plta/Negation.md %}).

It is straightforward to show that `suc m ≤ n` implies `m < n`,
and conversely.  One can then give an alternative derivation of the
properties of strict inequality, such as transitivity, by directly
exploiting the corresponding properties of inequality.

### Exercise (`<-trans`)

Show that strict inequality is transitive.

### Exercise (`trichotomy`) {#trichotomy}

Show that strict inequality satisfies a weak version of trichotomy, in
the sense that for any `m` and `n` that one of the following holds:
* `m < n`,
* `m ≡ n`, or
* `m > n`
This only involves two relations, as we define `m > n` to
be the same as `n < m`. You will need a suitable data declaration,
similar to that used for totality.  (We will show that the three cases
are exclusive after [negation]({{ site.baseurl }}{% link out/plta/Negation.md %}) is introduced.)

### Exercise (`+-mono-<`)

Show that addition is monotonic with respect to strict inequality.
As with inequality, some additional definitions may be required.

### Exercise (`≤-implies-<`, `<-implies-≤`)

Show that `suc m ≤ n` implies `m < n`, and conversely.

### Exercise (`<-trans′`)

Give an alternative proof that strict inequality is transitive,
using the relating between strict inequality and inequality and
the fact that inequality is transitive.


## Even and odd

As a further example, let's specify even and odd numbers.  Inequality
and strict inequality are *binary relations*, while even and odd are
*unary relations*, sometimes called *predicates*.
<pre class="Agda">{% raw %}<a id="18971" class="Keyword">data</a> <a id="even"></a><a id="18976" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#18976" class="Datatype">even</a> <a id="18981" class="Symbol">:</a> <a id="18983" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a> <a id="18985" class="Symbol">→</a> <a id="18987" class="PrimitiveType">Set</a>
<a id="18991" class="Keyword">data</a> <a id="odd"></a><a id="18996" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#18996" class="Datatype">odd</a>  <a id="19001" class="Symbol">:</a> <a id="19003" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a> <a id="19005" class="Symbol">→</a> <a id="19007" class="PrimitiveType">Set</a>

<a id="19012" class="Keyword">data</a> <a id="19017" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#18976" class="Datatype">even</a> <a id="19022" class="Keyword">where</a>
  <a id="even.zero"></a><a id="19030" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#19030" class="InductiveConstructor">zero</a> <a id="19035" class="Symbol">:</a> <a id="19037" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#18976" class="Datatype">even</a> <a id="19042" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a>
  <a id="even.suc"></a><a id="19049" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#19049" class="InductiveConstructor">suc</a>  <a id="19054" class="Symbol">:</a> <a id="19056" class="Symbol">∀</a> <a id="19058" class="Symbol">{</a><a id="19059" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#19059" class="Bound">n</a> <a id="19061" class="Symbol">:</a> <a id="19063" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="19064" class="Symbol">}</a> <a id="19066" class="Symbol">→</a> <a id="19068" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#18996" class="Datatype">odd</a> <a id="19072" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#19059" class="Bound">n</a> <a id="19074" class="Symbol">→</a> <a id="19076" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#18976" class="Datatype">even</a> <a id="19081" class="Symbol">(</a><a id="19082" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="19086" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#19059" class="Bound">n</a><a id="19087" class="Symbol">)</a>

<a id="19090" class="Keyword">data</a> <a id="19095" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#18996" class="Datatype">odd</a> <a id="19099" class="Keyword">where</a>
  <a id="odd.suc"></a><a id="19107" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#19107" class="InductiveConstructor">suc</a>   <a id="19113" class="Symbol">:</a> <a id="19115" class="Symbol">∀</a> <a id="19117" class="Symbol">{</a><a id="19118" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#19118" class="Bound">n</a> <a id="19120" class="Symbol">:</a> <a id="19122" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="19123" class="Symbol">}</a> <a id="19125" class="Symbol">→</a> <a id="19127" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#18976" class="Datatype">even</a> <a id="19132" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#19118" class="Bound">n</a> <a id="19134" class="Symbol">→</a> <a id="19136" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#18996" class="Datatype">odd</a> <a id="19140" class="Symbol">(</a><a id="19141" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="19145" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#19118" class="Bound">n</a><a id="19146" class="Symbol">)</a>{% endraw %}</pre>
A number is even if it is zero or the successor of an odd number,
and odd if it is the successor of an even number.

This is our first use of a mutually recursive datatype declaration.
Since each identifier must be defined before it is used, we first
declare the indexed types `even` and `odd` (omitting the `where`
keyword and the declarations of the constructors) and then
declare the constructors (omitting the signatures `ℕ → Set`
which were given earlier).

This is also our first use of *overloaded* constructors,
that is, using the same name for different constructors depending on
the context.  Here `suc` means one of three constructors:

    suc : `ℕ → `ℕ
    suc : ∀ {n : ℕ} → odd n → even (suc n)
    suc : ∀ {n : ℕ} → even n → odd (suc n)

Similarly, `zero` refers to one of two constructors. Due to how it
does type inference, Agda does not allow overloading of defined names,
but does allow overloading of constructors.  It is recommended that
one restrict overloading to related meanings, as we have done here,
but it is not required.

We show that the sum of two even numbers is even.
<pre class="Agda">{% raw %}<a id="e+e≡e"></a><a id="20274" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#20274" class="Function">e+e≡e</a> <a id="20280" class="Symbol">:</a> <a id="20282" class="Symbol">∀</a> <a id="20284" class="Symbol">{</a><a id="20285" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#20285" class="Bound">m</a> <a id="20287" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#20287" class="Bound">n</a> <a id="20289" class="Symbol">:</a> <a id="20291" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="20292" class="Symbol">}</a> <a id="20294" class="Symbol">→</a> <a id="20296" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#18976" class="Datatype">even</a> <a id="20301" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#20285" class="Bound">m</a> <a id="20303" class="Symbol">→</a> <a id="20305" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#18976" class="Datatype">even</a> <a id="20310" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#20287" class="Bound">n</a> <a id="20312" class="Symbol">→</a> <a id="20314" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#18976" class="Datatype">even</a> <a id="20319" class="Symbol">(</a><a id="20320" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#20285" class="Bound">m</a> <a id="20322" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="20324" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#20287" class="Bound">n</a><a id="20325" class="Symbol">)</a>
<a id="o+e≡o"></a><a id="20327" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#20327" class="Function">o+e≡o</a> <a id="20333" class="Symbol">:</a> <a id="20335" class="Symbol">∀</a> <a id="20337" class="Symbol">{</a><a id="20338" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#20338" class="Bound">m</a> <a id="20340" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#20340" class="Bound">n</a> <a id="20342" class="Symbol">:</a> <a id="20344" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="20345" class="Symbol">}</a> <a id="20347" class="Symbol">→</a> <a id="20349" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#18996" class="Datatype">odd</a>  <a id="20354" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#20338" class="Bound">m</a> <a id="20356" class="Symbol">→</a> <a id="20358" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#18976" class="Datatype">even</a> <a id="20363" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#20340" class="Bound">n</a> <a id="20365" class="Symbol">→</a> <a id="20367" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#18996" class="Datatype">odd</a>  <a id="20372" class="Symbol">(</a><a id="20373" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#20338" class="Bound">m</a> <a id="20375" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="20377" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#20340" class="Bound">n</a><a id="20378" class="Symbol">)</a>

<a id="20381" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#20274" class="Function">e+e≡e</a> <a id="20387" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#19030" class="InductiveConstructor">zero</a>     <a id="20396" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#20396" class="Bound">en</a>  <a id="20400" class="Symbol">=</a>  <a id="20403" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#20396" class="Bound">en</a>
<a id="20406" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#20274" class="Function">e+e≡e</a> <a id="20412" class="Symbol">(</a><a id="20413" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#19049" class="InductiveConstructor">suc</a> <a id="20417" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#20417" class="Bound">om</a><a id="20419" class="Symbol">)</a> <a id="20421" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#20421" class="Bound">en</a>  <a id="20425" class="Symbol">=</a>  <a id="20428" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#19049" class="InductiveConstructor">suc</a> <a id="20432" class="Symbol">(</a><a id="20433" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#20327" class="Function">o+e≡o</a> <a id="20439" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#20417" class="Bound">om</a> <a id="20442" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#20421" class="Bound">en</a><a id="20444" class="Symbol">)</a>

<a id="20447" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#20327" class="Function">o+e≡o</a> <a id="20453" class="Symbol">(</a><a id="20454" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#19107" class="InductiveConstructor">suc</a> <a id="20458" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#20458" class="Bound">em</a><a id="20460" class="Symbol">)</a> <a id="20462" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#20462" class="Bound">en</a>  <a id="20466" class="Symbol">=</a>  <a id="20469" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#19107" class="InductiveConstructor">suc</a> <a id="20473" class="Symbol">(</a><a id="20474" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#20274" class="Function">e+e≡e</a> <a id="20480" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#20458" class="Bound">em</a> <a id="20483" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#20462" class="Bound">en</a><a id="20485" class="Symbol">)</a>{% endraw %}</pre>
Corresponding to the mutually recursive types, we use two mutually recursive
functions, one to show that the sum of two even numbers is even, and the other
to show that the sum of an odd and an even number is odd.

This is our first use of mutually recursive functions.  Since each identifier
must be defined before it is used, we first give the signatures for both
functions and then the equations that define them.

To show that the sum of two even numbers is even, consider the evidence that the
first number is even. If it because it is zero, then the sum is even because the
second number is even.  If it is because it is the successor of an odd number,
then the result is even because it is the successor of the sum of an odd and an
even number, which is odd.

To show that the sum of an odd and even number is odd, consider the evidence
that the first number is odd. If it is because it is the successor of an even
number, then the result is odd because it is the successor of the sum of two
even numbers, which is even.

### Exercise (`o+o≡e`)

Show that the sum of two odd numbers is even.


<!--

## Formalising preorder

<pre class="Agda">{% raw %}<a id="21643" class="Keyword">record</a> <a id="IsPreorder"></a><a id="21650" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#21650" class="Record">IsPreorder</a> <a id="21661" class="Symbol">{</a><a id="21662" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#21662" class="Bound">A</a> <a id="21664" class="Symbol">:</a> <a id="21666" class="PrimitiveType">Set</a><a id="21669" class="Symbol">}</a> <a id="21671" class="Symbol">(</a><a id="21672" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#21672" class="Bound Operator">_≤_</a> <a id="21676" class="Symbol">:</a> <a id="21678" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#21662" class="Bound">A</a> <a id="21680" class="Symbol">→</a> <a id="21682" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#21662" class="Bound">A</a> <a id="21684" class="Symbol">→</a> <a id="21686" class="PrimitiveType">Set</a><a id="21689" class="Symbol">)</a> <a id="21691" class="Symbol">:</a> <a id="21693" class="PrimitiveType">Set</a> <a id="21697" class="Keyword">where</a>
  <a id="21705" class="Keyword">field</a>
    <a id="IsPreorder.reflexive"></a><a id="21715" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#21715" class="Field">reflexive</a> <a id="21725" class="Symbol">:</a> <a id="21727" class="Symbol">∀</a> <a id="21729" class="Symbol">{</a><a id="21730" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#21730" class="Bound">x</a> <a id="21732" class="Symbol">:</a> <a id="21734" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#21662" class="Bound">A</a><a id="21735" class="Symbol">}</a> <a id="21737" class="Symbol">→</a> <a id="21739" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#21730" class="Bound">x</a> <a id="21741" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#21672" class="Bound Operator">≤</a> <a id="21743" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#21730" class="Bound">x</a>
    <a id="IsPreorder.trans"></a><a id="21749" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#21749" class="Field">trans</a> <a id="21755" class="Symbol">:</a> <a id="21757" class="Symbol">∀</a> <a id="21759" class="Symbol">{</a><a id="21760" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#21760" class="Bound">x</a> <a id="21762" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#21762" class="Bound">y</a> <a id="21764" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#21764" class="Bound">z</a> <a id="21766" class="Symbol">:</a> <a id="21768" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#21662" class="Bound">A</a><a id="21769" class="Symbol">}</a> <a id="21771" class="Symbol">→</a> <a id="21773" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#21760" class="Bound">x</a> <a id="21775" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#21672" class="Bound Operator">≤</a> <a id="21777" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#21762" class="Bound">y</a> <a id="21779" class="Symbol">→</a> <a id="21781" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#21762" class="Bound">y</a> <a id="21783" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#21672" class="Bound Operator">≤</a> <a id="21785" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#21764" class="Bound">z</a> <a id="21787" class="Symbol">→</a> <a id="21789" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#21760" class="Bound">x</a> <a id="21791" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#21672" class="Bound Operator">≤</a> <a id="21793" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#21764" class="Bound">z</a>

<a id="IsPreorder-≤"></a><a id="21796" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#21796" class="Function">IsPreorder-≤</a> <a id="21809" class="Symbol">:</a> <a id="21811" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#21650" class="Record">IsPreorder</a> <a id="21822" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#1205" class="Datatype Operator">_≤_</a>
<a id="21826" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#21796" class="Function">IsPreorder-≤</a> <a id="21839" class="Symbol">=</a>
  <a id="21843" class="Keyword">record</a>
    <a id="21854" class="Symbol">{</a> <a id="21856" class="Field">reflexive</a> <a id="21866" class="Symbol">=</a> <a id="21868" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#5716" class="Function">≤-refl</a>
    <a id="21879" class="Symbol">;</a> <a id="21881" class="Field">trans</a> <a id="21887" class="Symbol">=</a> <a id="21889" href="{% endraw %}{{ site.baseurl }}{% link out/plta/Relations.md %}{% raw %}#6374" class="Function">≤-trans</a>
    <a id="21901" class="Symbol">}</a>{% endraw %}</pre>

-->


## Standard prelude

Definitions similar to those in this chapter can be found in the standard library.
<pre class="Agda">{% raw %}<a id="22038" class="Keyword">import</a> <a id="22045" href="https://agda.github.io/agda-stdlib/Data.Nat.html" class="Module">Data.Nat</a> <a id="22054" class="Keyword">using</a> <a id="22060" class="Symbol">(</a><a id="22061" href="https://agda.github.io/agda-stdlib/Data.Nat.Base.html#802" class="Datatype Operator">_≤_</a><a id="22064" class="Symbol">;</a> <a id="22066" href="https://agda.github.io/agda-stdlib/Data.Nat.Base.html#833" class="InductiveConstructor">z≤n</a><a id="22069" class="Symbol">;</a> <a id="22071" href="https://agda.github.io/agda-stdlib/Data.Nat.Base.html#875" class="InductiveConstructor">s≤s</a><a id="22074" class="Symbol">)</a>
<a id="22076" class="Keyword">import</a> <a id="22083" href="https://agda.github.io/agda-stdlib/Data.Nat.Properties.html" class="Module">Data.Nat.Properties</a> <a id="22103" class="Keyword">using</a> <a id="22109" class="Symbol">(</a><a id="22110" href="https://agda.github.io/agda-stdlib/Data.Nat.Properties.html#1902" class="Function">≤-refl</a><a id="22116" class="Symbol">;</a> <a id="22118" href="https://agda.github.io/agda-stdlib/Data.Nat.Properties.html#2095" class="Function">≤-trans</a><a id="22125" class="Symbol">;</a> <a id="22127" href="https://agda.github.io/agda-stdlib/Data.Nat.Properties.html#1952" class="Function">≤-antisym</a><a id="22136" class="Symbol">;</a> <a id="22138" href="https://agda.github.io/agda-stdlib/Data.Nat.Properties.html#2207" class="Function">≤-total</a><a id="22145" class="Symbol">;</a>
                                  <a id="22181" href="https://agda.github.io/agda-stdlib/Data.Nat.Properties.html#11056" class="Function">+-monoʳ-≤</a><a id="22190" class="Symbol">;</a> <a id="22192" href="https://agda.github.io/agda-stdlib/Data.Nat.Properties.html#10966" class="Function">+-monoˡ-≤</a><a id="22201" class="Symbol">;</a> <a id="22203" href="https://agda.github.io/agda-stdlib/Data.Nat.Properties.html#10810" class="Function">+-mono-≤</a><a id="22211" class="Symbol">)</a>{% endraw %}</pre>
In the standard library, `≤-total` is formalised in terms of
disjunction (which we define in Chapter [Connectives]({{ site.baseurl }}{% link out/plta/Connectives.md %})),
and `+-monoʳ-≤`, `+-monoˡ-≤`, `+-mono-≤` are proved differently than here
as well as taking as implicit arguments that here are explicit.

## Unicode

This chapter uses the following unicode.

    ≤  U+2264  LESS-THAN OR EQUAL TO (\<=, \le)
    ≥  U+2265  GREATER-THAN OR EQUAL TO (\>=, \ge)
    ˡ  U+02E1  MODIFIER LETTER SMALL L (\^l)
    ʳ  U+02B3  MODIFIER LETTER SMALL R (\^r)

The commands `\^l` and `\^r` give access to a variety of superscript
leftward and rightward arrows in addition to superscript letters `l` and `r`.
