Things I may need to think about in order to get my changes to `zf` merged:

Idea: Have `Abstract.hs` abstract over the backend.

* `stack` vs `nix`. I guess one prominent issue with nix may be deploying to windows. One should try to make both work, currently `Version.hs` is broken.

Future features:

* Lambdas
* Using LaTeX labels `\label{myTheorem}` as identifiers. These need to be processed in `Adapt.hs`
* Structs
* Inductive types

Features I may need, but not for now:

* Aliases to backend lean commands. These require a bit of thought.
* Aliases to other naproche commands. These also require a bit of thought. Should they be resolved parse-time? This is a complicated issue that Adrian would be able to help me with.

As is often the case, I should first try to *manually* do these things by hardcoding them or sth. After a while I might get some insight into how to do this properly.
