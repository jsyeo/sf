---
layout: page
title: About
permalink: /about/
---

How to host literal code.

In directory `sf/` the following:

	$ make clobber
    $ make
    $ make serve &

The visible page appears at

    localhost:4000/sf/<permalink>

For markdown commands see [Daring Fireball](
https://daringfireball.net/projects/markdown/syntax
).

Important git commands:

    git pull
    git commit -am "message"
    git push

[Unicode abbreviations](
https://github.com/agda/agda/blob/master/src/data/emacs-mode/agda-input.el#L194
).

    \to    →
    \u+    ⊎
    \all   ∀
    \x     ×
	x\_1   x₁
	x\_i   xᵢ

Bindings for [Agda mode](
http://agda.readthedocs.io/en/latest/tools/emacs-mode.html
)

    ?            create hole
    {!...!}      create holde
    C-c C-l      reload
    C-c C-c x    split on variable x 
    C-c C-space  fill in hole
    
