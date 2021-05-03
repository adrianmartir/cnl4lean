

I feel like writing a bachelors thesis explaining in detail the idea of topoi as 'the essence' of theories may be quite good. Why topoi are good is explained really easily: They are a generalized syntactical construct, with one excellent property: Transforming the models of one theory into models of another theory is precisel modelled by geometric morphisms, which can be thought of as *generalized interpretations*(this should be some sort of 2-Yoneda lemma). This is the key technical property distinguishing topoi from something like geometric categories. And I should discuss it throughly.

Maybe a better perspective is geometric logic + geometric constructions, where geometric constructions can be something like
* Natural numbers,
* Free stuff in algebraic theories (eg. free modules over universal field)
* simple functions
* Glueings: locally f.p. Schemes

In fact, I may not even need to define adjunctions and instead define geometric morphisms as LEX, colimit preserving functors. Logically, that is a much better intuition. Discussions of Diaconescu equivalence and all the flat functor stuff and presheaf topoi as colimit-completions should all be done by closely motivating them by logic. I feel like there is a good piece of text to be written about all that stuff, with the unique logical perspective in mind. It gives all that abstract nonsense some very concrete grounding.

Also, I do not need any completeness theorems. Because completeness is trivial if not restricted to Set-models. Moreover, for proving classifying topos stuff, I won't use completeness and instead use interpretations. The reason is that (generalized) interpretations are more 'computational' and 'syntactic'. I find them more intuitive.

I should also talk about presheaf completions do not only contain formulas. Examples like the projective space might be interesting.

## Examples

Perhaps the most exiting thing about categorical logic are examples. How does categorical logic reflect the usual model-theoretic notions?

Moreover, I'd like to write simple algorithms based on that and benchmark them.

* Category of matrices(\equiv fp vector spaces \equiv fp vector spaces^{op}) is regular -> regular logic of linear equations is easy. Gaussian elimination as a normal form?
* Vector spaces with poset structure? The SMT community seems to have some interest in this kind of thing.
* Steal more stuff from the SMT community.
* What other simple algebraic theories have the property that the fp models are regular?
* Geometric(regular, coherent, ...) functors between geometric (regular, coherent, ...) syntactic categories are interpretiations! Use the boolean algebra example, where we can axiomatize it with `and` and `not` or with `and` and `or`.
* Simple galois theory example?
* Equivalence between definable sets on the simple functions and the underlying boolean algebra (theory of rings and theory of boolean algebras, recover the boolean algebra as the set of idempotents)
* Representation theoretic morita-equivalences? Quivers and basic algebras. G-actions and modules over the corresponding group ring. Note that given enough points, two categories of R-modules are equivalent if and only if their corresponding theories are Morita-equivalent.
* Affine spaces and tarskian geometry? (as in the `geometry.ftl.tex` example)
* Equivalences of pretopoi(pretopoi are the suitable context for coherent logic with 'quotient types'(every equivalence rel is effective) and 'finite coproduct types'(=W-types?) ). Here I would like to show many equivalences for 'computer-sciency' theories: arrays, lists, doubly linked lists, heaps, sets, fibonacci heaps, trees, ....

* Conservativity of cartesian(regular, coherent, geometric) categories inside their Morleyizations(theories with formal negations)
* My results on interpretations
* Johnstones 'Stone Spaces' has many results on lattices. E.g. many different axiomatizations of distributive lattices, boolean algebras, meet semilattices, join semilattices (algebraic and poset-based)
* Steal olivias stuff
* Maybe a couple of the theories associated to commonly used Freer monads are suitable.

* Cartesian theories: Write an algorithms for normalization of theories of terms in monoids, groups, rings, k-algebras...(for k-algebras we should use two different normal forms: First, polynomials, and then the Horner normal form)

Probably one of the most interesting things is how cartesian categories can be used to implicitly enforce a normal form on the terms.

## What is this thesis about?

I think I am getting a pretty good idea of what this thesis should be about. It should mainly be establishing the most basic results in topos theory and then simply being a database of examples. I want to collect many, many examples of bridges and functors in the logic literature.

One of the things I want to do is for each example choose the smallest possible class of syntactic categories(eg. first try cartesian) and then state the equivalence on that level. The reason is that topoi have no good 'calculus' that lets them concisely describe every sheaf with a formula. Why? Because we need to index coproducts over *any set in the metatheory*. This is not so good.

https://ncatlab.org/nlab/show/pretopos

Thus, if one wants to compute bridges one should use something like a W-pretopos and restrict oneself to coherent logic. Or one could build a custom theory for constructing the index sets for coproducts(theory of real numbers or sth). Hm \Pi-pretopoi seem bad. They probably (just like first order sites) don't induce the right category of models, one would then get some assumption like 'elementary morphism'. **This essentially means that we want to restrict ourselves to constructions and logic that get preserved by every model homomorphism**. This is the key to everything. We want to do mathematics that is preserved by all homomorphisms. *This should actually be the whole motivation of the paper - Doing logic with exteremely well-behaved model theory*.

Perhaps a fix the problem where we index over all sets makes things incomputable is working internally to a classifying topos of a theory T with universal model U. Then we specify that we want to construct(internally) a pretopos and also allow coproducts indexed by subobjects of U(i.e. geometric formulas over the context with one variable). Then we can use the Grothendieck construction in order to keep things nice and finitely axiomatized(is this a good idea?).

---

I should use the 'question.tex' file for motivation in the cartesian theories chapter!!!!

## Structure

* Cartesian theories and cartesian categories
* Regular theories and regular categories
* Regular theories with quotients and regular effective categories
* Coherent theories and coherent categories
* Coherent theories with quotients and finite coproducts and pretopoi
* Coherent theories with quotients and W-types and W-pretopoi (As a universe for programming languages!!)

* Geometric theories and topoi (go into topology, frames things like stone duality, group actions/galois theory)

The meat should consist of examples for all that shit, as listed above.

## Extract from the log on 29-03-2021

Okay, *my intuition* above was pretty misguided. I have figured it out now. Say you want to write a program where you have some sort of ADT to model your domain. Then you add your functions, write your laws into the documentation. What you now want to do is write down your algebraic theory (Cartesian should be a useful relaxation, after all partial operations happen all the time in programming. Better than throwing errors lolololol). Then you look at some sort of syntactic category(or pretopos-completion, which still has no ADTs) of the theory. Everything useful in that particular domain should simply be operations in that category. Then, when you want to represent it a different way, or interpret it into another domain, you simply define the corresponding structure-preserving functor. So the question of whether ADTs get preserved by geometric morphisms is entirely irrelevant.

I am very convinced that this works very well. It should be the canonical way to write code. I can imagine that for instance one can relate all the different datastructures (HashMaps, Lists, Sets, etc.)  by doing this.

## Extract from the log on 11-02-2021

The exporter must be more stupid. That is the solution. It can't know about the semantics of patterns -> lean translations and whatnot. Thus, every time the exporter runs into a pattern that is supposed to be defined elsewhere, it writes it into backtick syntax. Every time the exporter runs into a new definition, it translates it into a backtick syntax macro. This is so much simpler than the above. Thus, the pattern to lean term translations simply become plain old lean files with some metaprogramming. So with this, we avoid needing to push around extensive exporter configurations, right?

Not entirely right. What about vocabularies? I think nave needs to know about all the vocabularies it depends on. So technically, we would need to develop some sort of vocabulary dependency system. What a pain. I don't want to do this. The good news is that *vocabulary specifications* happen on a *per-project basis*. For example, say I want to use a category theory lean library. Then I write some sort of *wrapper projects*, that defines the vocabulary for the category theory library and moreover gives the lean bindings in the form of a lean file. Then I put this project on github and start a new project that has the category theory wrapper project as a dependency. This would mean that for each project there is a file `nave.yaml` that specifies where the vocabulary and the lean bindings are located, and moreover specifies all dependencies on github(that themselves also have a `nave.yaml`). Then there is a nix expression that uses `nave.yaml` in order to fetch all dependencies to the nix store and then calls nave with the needed *vocabulary specifications* and later calls lean with the needed *pattern definitions*.

Ahhhhrggghh. Notice the lack of namespacing. I mean mathematics has never had namespacing lol. But nameclashes are probably inevitable. *This is beginning to feel like we need a module system again. This is bad news*. We don't want that. Maybe this hints at the fact, we don't want 'global' pattern definitions as I suggested above.

Actually, namespacing might not be an issue at all for *vocabularies*, since vocabularies should not ever be conflicting. They simply state the gramatical functions of words. There is no space for conflicts there. The complications come when using *pattern to lean translations*. But there, one can easily reuse the lean module system. Thus we are saved.

---

Perhaps one should compile not to lean as a user might traditionally use it, but rather to 'elaborated lean'. This is low level and thus better.

## Questions:

* How much should be in natural language? Since I don't want to be too ambitious, I clearly only will have a small number of features available in CNL. But what is the long-term plan? Does natural language lead to bad engineering? Like, tactics should not be written in CNL, ever.

Hmmmmmmm, we somehow need a connection between 'nouns' and 'symbolic latex terms'. The problem is that you can easily construct a definition of something like a group on the term level(with tuples). But then you need to actually call it 'group' and use it as a noun. It seems to me that that is not yet possible.

We need something like 'aliases', like 'let bla stand for bla.', like in naproche.
