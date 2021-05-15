
## Thesis

My thesis will inevitably contain:


* Background on interactive theorem provers, naproche and Adrian's new parser
* Architecture of my program
* Philosophy: Relatively thin sugar above lean, little automation (the Lean philosophy)
* Propositions, predicates types and statement/assumption semantics - Do many examples
* Structures and inductives - Embedd examples
* Typeclasses for subtyping - Embedd examples

* OPTIONAL: Stress test - the yoneda lemma and limits and colimits

## Vision

The goal of this project is to make formalizations readable for mathematicians with no training in ITPs. Why?

Giving formal semantics to theorems and definitions allows us to do the following:

* Reduce ambiguity: When reading papers outside ones area of expertise, it often is a problem figuring out which conventions and notations the author is using. Or whether they missed a statement like *From now on, let all rings be noetherian* 50 pages prior.

* Clickability: Papers are often read by first reading the main theorem and then trying to hunt around the relevant lemma and definitions in order to understand it. With a formalization in my style, one could theoretically just click on the relevant definition.

-> Partial formalization makes mathematical text much easier to read. Especially with people who are not already familiar with the material.

* Searchability

* Trustworthiness and scaling

---

https://jiggerwit.wordpress.com/2019/06/20/an-argument-for-controlled-natural-languages-in-mathematics/
* Use leans white-box automation philosophy. It is impossible to write scalable formalizations without expertise. In 4b of Hales' essay, he cites Steven Watt saying *there is a difference between watching a movie and directing a movie*


### Formalization, community projects and big references.

There is a strong case to be made for organizing large volumes of mathematical content in a formalized format.

Examples:
* Johnstone's Sketches of an Elephant
* Fremlin's Measure Theory
* nlab
* Stacks project

Problems these projects should solve:
* Standardizing conventions
* Black-boxing results
* Trustworthyness of results

I would argue that these encyclopedia-style projects should be in some sort of formalized format. More concretely, I would want them to consist of the following two components:

1. A documentation page that contains formal definitions and theorem statements. Proofs are given in a *heavily informal and abstracted manner*, like "this is a standard gluing argument" or "we can do the same as in 2.3.43, but we need to be careful with the following technical issue". Proofs should favour readability above everything else.
2. A *backend* where the proofs are given more precisely in non-human language, i.e. lean tactics

What does this workflow mean for the reader? The reader can browse the database of theorems by reading the documentation page. He will be able to
* Easily extract precise meaning and click through definitions he doesn't understand
* while ignoring proofs
* and completely trusting every result.

It perfectly fullfills the role of a big reference.

### Trustworthyness and Scaling

The main argument for formalization is trustworthyness. That argument is often refuted by saying that, if someone smart tells you *Fermat's Last Theorem* has been proven, then you trust him. You don't need a formal proof, since there is an overwhelming probability that the smart person is right.

And I would agree with this refutation. I would say that formalize a proof of *Fermat's Last Theorem* for the sake of being more certain in the correctness of the proof, is not reasonable.

But there is a different situation, where trustworthyness is much more valueable. Say you are reading an obscure nlab page and it just claims that something is true. Can I trust it? No, there are many instances where nlab has been wrong. You can edit pages on nlab anonymously, so there is no particular reason the result should be trusted. The only way you can trust it, is if you write down a proof yourself. Assuring yourself that the result is correct costs a huge amount of time and effort, and it is virtually impossible to do if you don't have the necessary expertise.

This means that effectively using results from a community mathematical reference can require tremendous expertise. Projects like Johnstone's Elephant and Fremlin's Measure Theory are trusted, precisely because they are *one-man projects*, and you trust the author.

I know, the mere suggestion of using results you don't fully understand is almost a taboo in mathematics education. To ilustrate how absurd the situation is, let's say you started learning computer science and someone suggested the following:

"I need to understand how gcc works in order to compile my C++ program"

That person would be laughed out of the room. That statement cannot be taken seriously.

To give a more concrete example of how this applies to mathematics, I want to raise the following question:

Why do we insist on learning algorithms for computing things in mathematics, when a computer could do it better than you ever would? It just doesn't make sense.

This is a sketch of the case I want to make for formalized references. This should be substatiated with a nontrivial example, i.e. my bachelors thesis.
